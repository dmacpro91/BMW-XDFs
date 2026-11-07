#!/usr/bin/env python3
"""
xdftool.py - TunerPro XDFs for the BMW S68 DME (Bosch MG1CS221 / DME9: X5 M, M5), from an A2L.

The software (ASW, SWFL) fixes where every calibration table sits; calibrations (SWFK) for the
same software only differ in values. So there is one XDF per SWFL, and `port` is only needed
when the software changes. `xdftool.py COMMAND -h` for details. Stdlib only.
"""
import argparse
import bisect
import collections
import decimal
import difflib
import hashlib
import html
import io
import json
import os
import pickle
import re
import struct
import sys
import tempfile
import xml.etree.ElementTree as ET
import zipfile
import zlib

# ============================================================================
# MG1CS221 flash layout (S68 DME9). A full read is 10 MiB; bin offset 0 = 0x80000000.
# ============================================================================

BASE = 0x80000000                 # 0xA0000000 is the uncached alias of the same flash
CAL = (0x90000, 0x190000)         # calibration data
SWFL_RECORD = 0x18FB0A            # 8 bytes: process class 08, SWFL id, main/sub/patch version


def read_bin(path):
    with open(path, 'rb') as f:
        return f.read()


def software_id(data):
    """The SWFL of the cal logistics block, e.g. '0000752714961E' - the repo's folder names."""
    return data[SWFL_RECORD + 1:SWFL_RECORD + 8].hex().upper()


def diff_offsets(a, b, lo=0, hi=None, chunk=4096):
    """Offsets where a and b differ, comparing whole chunks first."""
    hi = min(len(a), len(b)) if hi is None else hi
    out = []
    for i in range(lo, hi, chunk):
        j = min(i + chunk, hi)
        if a[i:j] != b[i:j]:
            out.extend(k for k in range(i, j) if a[k] != b[k])
    return out


def variant(data):
    """BMW's description of the calibration, e.g. 'S68B44T0-PVL-G90H-USA-KOR---ULEV70-AWD-430kW_750Nm':
    engine, car, market, emissions standard, power."""
    m = re.search(rb'##DME-\w+-(?:M-)?([\x21-\x7e]+?)_{2,}', data[CAL[0]:CAL[1]])
    return m.group(1).decode() if m else ''


def find_svk(data):
    """
    SGBM ids in the cal logistics block that ends in '#DME...':
        [0D <SWFK id:4> <ver:3>] (S68)   <n> 08 <SWFL id:4> <main sub patch>   02 <HWEL id:4> FF FF FF ...
    -> [(offset, 'SWFL' or 'SWFK', 'IIIIIIIIMMSSPP')]
    """
    out, seen = [], set()
    for m in re.finditer(rb'#DME[-_]', data):
        start = max(0, m.start() - 0x60)
        for pc, kind in ((0x08, 'SWFL'), (0x0D, 'SWFK')):
            for mm in re.finditer(bytes([pc]) + rb'\x00\x00', data[start:m.start()]):
                rec = data[start + mm.start():start + mm.start() + 8]
                svk = rec[1:].hex().upper()
                if len(rec) == 8 and rec[5:] != b'\xff\xff\xff' and (kind, svk) not in seen:
                    seen.add((kind, svk))
                    out.append((start + mm.start(), kind, svk))
    return out


# ============================================================================
# Reading XDFs
# ============================================================================

LABEL_RE = re.compile(r'\s*([A-Za-z_][A-Za-z0-9_.\[\]]*)')


def evaluate(eq, x):
    """A TunerPro MATH equation in X."""
    try:
        return eval(eq, {'__builtins__': {}}, {'X': float(x)})
    except Exception:
        return float(x)


def _is_number(s):
    try:
        float(s)
        return True
    except ValueError:
        return False


class Element:
    """One addressed block of a table: its z data or a stored axis."""

    def __init__(self, role, emb, eq='X', count=None):
        self.role = role
        self.address = int(emb['mmedaddress'], 16)
        self.bits = int(emb.get('mmedelementsizebits', 8))
        self.flags = int(emb.get('mmedtypeflags', '0'), 16)
        rows, cols = int(emb.get('mmedrowcount', 1)), int(emb.get('mmedcolcount', count or 1))
        self.n = rows * cols if role == 'z' else (count or cols)
        self.step = self.bits // 8
        self.size = self.n * self.step
        self.eq = eq

    def raw(self, data, address=None):
        a = self.address if address is None else address
        out = []
        for i in range(a, a + self.size, self.step):
            b = data[i:i + self.step]
            if self.flags & 0x10000:
                out.append(struct.unpack('<f' if self.step == 4 else '<d', b)[0])
            else:
                out.append(int.from_bytes(b, 'little' if self.flags & 0x02 else 'big', signed=bool(self.flags & 1)))
        return out

    def phys(self, data, address=None):
        return [evaluate(self.eq, x) for x in self.raw(data, address)]


class Table:
    def __init__(self, title, desc, cats, elements, units, row_labels):
        self.title, self.desc, self.cats = title, desc, cats
        self.elements, self.units, self.row_labels = elements, units, row_labels

    @property
    def label(self):
        """The A2L label the description starts with ('' for hand-made tables)."""
        m = LABEL_RE.match(self.desc)
        return m.group(1) if m else ''

    @property
    def key(self):
        """What identifies the table across software versions: its A2L label, else its title."""
        return self.label or self.title

    @property
    def z(self):
        return next(e for e in self.elements if e.role == 'z')

    def cells(self):
        """{key: (address, size)}. A one-column table with text row labels (a fault array) has one
        cell per row, keyed by the label's first word (the fault name); any other table one cell
        per element."""
        z = self.z
        if self.row_labels and len(self.row_labels) == z.n:
            return {lab.split()[0]: (z.address + i * z.step, z.step) for i, lab in enumerate(self.row_labels)}
        return {(e.role, i): (e.address, e.size) for i, e in enumerate(self.elements)}


def load_xdf(path, autogen=False):
    """-> ({category id: name}, [Table]). Category ids are what CATEGORYMEM uses (index + 1).
    The '(autogen)' breakpoint tables are left out unless autogen=True."""
    root = ET.parse(path).getroot()
    cats = {int(c.get('index'), 16) + 1: c.get('name') for c in root.iter('CATEGORY')}
    tables = []
    for tbl in root.iter('XDFTABLE'):
        title = (tbl.findtext('title') or '').strip()
        if title.endswith('(autogen)') and not autogen:
            continue
        elements, units, row_labels = [], '', []
        for ax in tbl.findall('XDFAXIS'):
            role, emb = ax.get('id'), ax.find('EMBEDDEDDATA')
            labels = [lab.get('value', '') for lab in ax.findall('LABEL')]
            if emb is None or 'mmedaddress' not in emb.attrib:
                if role == 'y' and not all(_is_number(v) for v in labels):
                    row_labels = labels
                continue
            math = ax.find('MATH')
            count = ax.findtext('indexcount')
            elements.append(Element(role, emb.attrib, math.get('equation', 'X') if math is not None else 'X',
                                    int(count) if count else None))
            if role == 'z':
                units = ax.findtext('units') or ''
        if any(e.role == 'z' for e in elements):
            tables.append(Table(title, tbl.findtext('description') or '',
                                [int(m.get('category')) for m in tbl.findall('CATEGORYMEM')],
                                elements, units, row_labels))
    return cats, tables


def category(cats, table):
    return next((cats[c] for c in table.cats if c in cats), '')


def pair_tables(tables, others):
    """[(table, twin or None)]: each table with the same-key table of another XDF, the n-th
    occurrence of a key pairing with the n-th."""
    by_key, seen, out = {}, {}, []
    for t in others:
        by_key.setdefault(t.key, []).append(t)
    for t in tables:
        k = seen[t.key] = seen.get(t.key, -1) + 1
        cands = by_key.get(t.key, [])
        out.append((t, cands[k] if k < len(cands) else None))
    return out


def fmt_range(v):
    if not v:
        return '-'
    lo, hi = min(v), max(v)
    f = lambda x: ('%d' % x) if float(x).is_integer() else ('%.6g' % x)
    return f(lo) if lo == hi else '%s..%s' % (f(lo), f(hi))


# ============================================================================
# A2L parsing
# ============================================================================

# A string may contain doubled quotes ("" = ") and then runs to the quote ending the line.
_STR = r'"(?:[^"\n]|"")*""(?:[^"\n]|"")*"(?=[ \t]*\r?$)|"(?:[^"\\]|\\.)*"'
TOKEN_RE = re.compile(_STR + r'|\S+', re.M)
COMMENT_RE = re.compile(r'(' + _STR + r')|/\*.*?\*/|//[^\n]*', re.S | re.M)

# name: (size in bytes, signed, float)
DTYPES = {
    'UBYTE': (1, False, False), 'SBYTE': (1, True, False),
    'UWORD': (2, False, False), 'SWORD': (2, True, False),
    'ULONG': (4, False, False), 'SLONG': (4, True, False),
    'A_UINT64': (8, False, False), 'A_INT64': (8, True, False),
    'FLOAT32_IEEE': (4, True, True), 'FLOAT64_IEEE': (8, True, True),
}
ALIGN_KEY = {'UBYTE': 'BYTE', 'SBYTE': 'BYTE', 'UWORD': 'WORD', 'SWORD': 'WORD',
             'ULONG': 'LONG', 'SLONG': 'LONG', 'A_UINT64': 'INT64', 'A_INT64': 'INT64'}

# Optional keywords that may follow the fixed fields of a block. Anything after one of these
# belongs to it, so the set must be complete enough that stray tokens don't get misattributed.
KEYWORDS = {
    'COEFFS', 'COEFFS_LINEAR', 'COMPU_TAB_REF', 'FORMULA', 'REF_UNIT', 'STATUS_STRING_REF',
    'FORMAT', 'PHYS_UNIT', 'NUMBER', 'MATRIX_DIM', 'BIT_MASK', 'BYTE_ORDER', 'DISPLAY_IDENTIFIER',
    'EXTENDED_LIMITS', 'READ_ONLY', 'GUARD_RAILS', 'ECU_ADDRESS_EXTENSION', 'CALIBRATION_ACCESS',
    'COMPARISON_QUANTITY', 'MAX_REFRESH', 'REF_MEMORY_SEGMENT', 'SYMBOL_LINK', 'STEP_SIZE',
    'DEPOSIT', 'MONOTONY', 'AXIS_PTS_REF', 'CURVE_AXIS_REF', 'FIX_AXIS_PAR', 'FIX_AXIS_PAR_DIST',
    'FIX_AXIS_PAR_LIST', 'MAX_GRAD', 'ENCODING', 'MODEL_LINK', 'DEPENDENT_CHARACTERISTIC',
    'VIRTUAL_CHARACTERISTIC', 'DISCRETE', 'ANNOTATION', 'FUNCTION_LIST', 'MAP_LIST', 'ALIAS',
}


def _unq(tok):
    return tok[1:-1].replace('""', '"') if len(tok) >= 2 and tok[0] == tok[-1] == '"' else tok


def _num(tok):
    if tok.lower().startswith('0x'):
        return int(tok, 16)
    try:
        return int(tok)
    except ValueError:
        return float(tok)


def _block_re(kind):
    return re.compile(r'/begin\s+%s\b(.*?)/end\s+%s\b' % (kind, kind), re.S)


def _blocks(text, kind):
    """Token lists of every /begin KIND ... /end KIND block."""
    return [TOKEN_RE.findall(m.group(1)) for m in _block_re(kind).finditer(text)]


def _kw(tokens, start):
    """Optional trailing keywords -> {KEYWORD: [args]}."""
    out, cur = {}, None
    for t in tokens[start:]:
        if t in ('/begin', '/end'):
            continue
        if t in KEYWORDS:
            cur = out.setdefault(t, [])
        elif cur is not None:
            cur.append(t)
    return out


def _first(kw, key, conv=_unq):
    return conv(kw[key][0]) if kw.get(key) else None


class A2L:
    def __init__(self):
        self.project = ''
        self.alignment = {'BYTE': 1, 'WORD': 2, 'LONG': 4, 'INT64': 4,
                          'FLOAT32_IEEE': 4, 'FLOAT64_IEEE': 4}
        self.record_layouts = {}
        self.compu_methods = {}
        self.axis_pts = {}
        self.characteristics = {}
        self.unscaled = set()  # COMPU_METHODs whose scaling could not be expressed (raw values used)

    @classmethod
    def load(cls, path, cache=True):
        """Parse an A2L. The result is cached in the temp dir, keyed by path, mtime and size."""
        st = os.stat(path)
        key = '%s|%d|%d|v3' % (os.path.abspath(path), st.st_mtime_ns, st.st_size)
        cpath = os.path.join(tempfile.gettempdir(),
                             'xdftool-a2l-%s.pickle' % hashlib.sha1(key.encode()).hexdigest())
        a = cls()
        if cache and os.path.exists(cpath):
            try:
                with open(cpath, 'rb') as f:
                    a.__dict__.update(pickle.load(f))
                return a
            except Exception:
                pass
        a._parse(path)
        if cache:
            try:
                with open(cpath, 'wb') as f:
                    pickle.dump(a.__dict__, f, protocol=pickle.HIGHEST_PROTOCOL)
            except OSError:
                pass
        return a

    def _parse(self, path):
        with open(path, 'rb') as f:
            text = f.read().decode('latin-1')
        text = COMMENT_RE.sub(lambda m: m.group(1) or ' ', text)
        for big in ('A2ML', 'IF_DATA'):  # huge and irrelevant
            text = _block_re(big).sub(' ', text)

        m = re.search(r'/begin\s+PROJECT\s+(\S+)', text)
        self.project = m.group(1) if m else ''

        for toks in _blocks(text, 'MOD_COMMON'):
            for i, t in enumerate(toks):
                if t.startswith('ALIGNMENT_'):
                    self.alignment[t[len('ALIGNMENT_'):]] = int(toks[i + 1])

        for toks in _blocks(text, 'RECORD_LAYOUT'):
            items = []
            for i, t in enumerate(toks[1:], 1):
                nxt = toks[i + 1:i + 4]
                if t.startswith('FIX_NO_AXIS_PTS_'):
                    items.append({'kind': t, 'n': int(nxt[0])})
                elif len(nxt) >= 2 and nxt[0].isdigit() and nxt[1] in DTYPES:
                    item = {'kind': t, 'pos': int(nxt[0]), 'dtype': nxt[1]}
                    if t == 'FNC_VALUES':
                        item['dir'] = nxt[2]
                    items.append(item)
            self.record_layouts[toks[0]] = items

        for toks in _blocks(text, 'COMPU_METHOD'):
            kw = _kw(toks, 5)
            self.compu_methods[toks[0]] = {
                'type': toks[2], 'format': _unq(toks[3]), 'unit': _unq(toks[4]),
                'coeffs': [float(x) for x in kw.get('COEFFS', [])[:6]],
                'coeffs_linear': [float(x) for x in kw.get('COEFFS_LINEAR', [])[:2]],
            }

        for toks in _blocks(text, 'AXIS_PTS'):
            kw = _kw(toks, 10)
            self.axis_pts[toks[0]] = {
                'name': toks[0], 'address': _num(toks[2]), 'layout': toks[4], 'conv': toks[6],
                'max_points': int(toks[7]), 'phys_unit': _first(kw, 'PHYS_UNIT')}

        axis_re = _block_re('AXIS_DESCR')
        for m in _block_re('CHARACTERISTIC').finditer(text):
            body = m.group(1)
            toks = TOKEN_RE.findall(axis_re.sub(' ', body))
            kw = _kw(toks, 9)
            ch = {'desc': _unq(toks[1]), 'type': toks[2], 'address': _num(toks[3]),
                  'layout': toks[4], 'conv': toks[6], 'lower': _num(toks[7]), 'upper': _num(toks[8]),
                  'number': _first(kw, 'NUMBER', int), 'phys_unit': _first(kw, 'PHYS_UNIT'),
                  'matrix_dim': [int(x) for x in kw.get('MATRIX_DIM', [])], 'axes': []}
            for am in axis_re.finditer(body):
                at = TOKEN_RE.findall(am.group(1))
                akw = _kw(at, 6)
                ch['axes'].append({
                    'attr': at[0], 'input': at[1], 'conv': at[2], 'max_points': int(at[3]),
                    'ref': _first(akw, 'AXIS_PTS_REF', str), 'phys_unit': _first(akw, 'PHYS_UNIT'),
                    'fix_par': [_num(x) for x in akw.get('FIX_AXIS_PAR', [])[:3]],
                    'fix_dist': [_num(x) for x in akw.get('FIX_AXIS_PAR_DIST', [])[:3]],
                    'fix_list': [_num(x) for x in akw.get('FIX_AXIS_PAR_LIST', [])
                                 if re.match(r'^[-+0-9.]', x)],
                })
            self.characteristics[toks[0]] = ch
        self._lower = {k.lower(): k for k in self.characteristics}

    def find(self, name):
        """The CHARACTERISTIC called name, matched case-insensitively if need be -> (name, dict)."""
        if name not in self.characteristics:
            name = self._lower[name.lower()]
        return name, self.characteristics[name]

    def align(self, dtype):
        return self.alignment.get(ALIGN_KEY.get(dtype, dtype), 1)

    def compu(self, name):
        """(equation in X turning raw into physical, unit, decimal places)."""
        cm = self.compu_methods.get(name)
        if cm is None:
            return 'X', '', None
        unit, t = cm['unit'], cm['type']
        m = re.match(r'%\s*\d*\.(\d+)', cm['format'])
        dec = int(m.group(1)) if m else None
        if t == 'LINEAR' and cm['coeffs_linear']:
            return _lin_eq(*cm['coeffs_linear']), unit, dec
        if t == 'RAT_FUNC' and cm['coeffs']:
            # raw = (a p^2 + b p + c) / (d p^2 + e p + f); invert the linear cases for p
            a, b, c, d, e, f = cm['coeffs']
            if a == 0 and d == 0 and e == 0 and b:
                return _lin_eq(f / b, -c / b), unit, dec
            if a == 0 and d == 0 and e:
                return '(%s-%s*X)/(%s*X-%s)' % (_f(c), _f(f), _f(e), _f(b)), unit, dec
        if t == 'TAB_VERB':
            return 'X', unit, 0
        if t != 'IDENTICAL':
            self.unscaled.add(name)
        return 'X', unit, dec


def _f(v):
    return str(int(v)) if float(v).is_integer() else repr(float(v))


def _lin_eq(a, b):
    """phys = a*X + b as a TunerPro equation."""
    s = 'X' if a == 1 else 'X*%s' % _f(a)
    if b > 0:
        s += '+%s' % _f(b)
    elif b < 0:
        s += '-%s' % _f(-b)
    return s



class Bin:
    """A flash read, addressed the way the A2L does (offset 0 = BASE; 0xA... is the uncached alias)."""

    def __init__(self, path, base=BASE):
        self.data = read_bin(path)
        self.base = base

    def off(self, addr):
        if addr & 0xE0000000 == 0xA0000000:
            addr ^= 0x20000000
        o = addr - self.base
        if not 0 <= o < len(self.data):
            raise ValueError('address 0x%X outside bin' % addr)
        return o

    def read(self, addr, dtype):
        size, signed, flt = DTYPES[dtype]
        o = self.off(addr)
        raw = self.data[o:o + size]
        if flt:
            return struct.unpack('<f' if size == 4 else '<d', raw)[0]
        return int.from_bytes(raw, 'little', signed=signed)


# ============================================================================
# A2L characteristic -> table
# ============================================================================

class Unsupported(Exception):
    pass


def _layout_offsets(a2l, items, counts):
    """Byte offset of each record-layout element, given axis point counts {'X','Y','FNC'}."""
    off, res = 0, {}
    for it in sorted((i for i in items if 'pos' in i), key=lambda i: i['pos']):
        size = DTYPES[it['dtype']][0]
        al = a2l.align(it['dtype'])
        off += -off % al
        res[it['kind']] = off
        if it['kind'].startswith('AXIS_PTS_'):
            off += size * counts.get(it['kind'][-1], 1)
        elif it['kind'] == 'FNC_VALUES':
            off += size * counts.get('FNC', 1)
        else:
            off += size
    return res


def _stored_count(a2l, b, addr, items, kinds, letter, max_points, counts):
    """Actual number of axis points stored in the bin (NO_AXIS_PTS_*), else max_points."""
    key = 'NO_AXIS_PTS_' + letter
    if key not in kinds:
        return max_points
    stored = b.read(addr + _layout_offsets(a2l, items, counts)[key], kinds[key]['dtype'])
    return stored if 0 < stored <= max_points else max_points


def _addr_axis(address, dtype, count, conv_result, unit, name):
    eq, cunit, dec = conv_result
    return {'kind': 'addr', 'address': address, 'dtype': dtype, 'count': count, 'eq': eq,
            'unit': unit or cunit, 'dec': dec, 'name': name}


def _com_axis(a2l, b, ap):
    items = a2l.record_layouts.get(ap['layout'], [])
    kinds = {i['kind']: i for i in items}
    if 'AXIS_PTS_X' not in kinds:
        raise Unsupported('AXIS_PTS without AXIS_PTS_X: %s' % ap['name'])
    n = _stored_count(a2l, b, ap['address'], items, kinds, 'X', ap['max_points'], {'X': 0})
    offs = _layout_offsets(a2l, items, {'X': n})
    return _addr_axis(ap['address'] + offs['AXIS_PTS_X'], kinds['AXIS_PTS_X']['dtype'], n,
                      a2l.compu(ap['conv']), ap['phys_unit'], ap['name'])


def _fix_axis(a2l, ax):
    eq, unit, dec = a2l.compu(ax['conv'])
    if ax['fix_list']:
        vals = ax['fix_list']
    elif ax['fix_par']:
        o, s, n = ax['fix_par']
        vals = [o + k * 2 ** s for k in range(int(n))]
    elif ax['fix_dist']:
        o, d, n = ax['fix_dist']
        vals = [o + k * d for k in range(int(n))]
    else:
        raise Unsupported('fix axis without params')
    labels = [evaluate(eq, v) for v in vals]
    return {'kind': 'labels', 'labels': labels, 'count': len(labels),
            'unit': ax['phys_unit'] or unit, 'dec': dec}


def resolve(a2l, b, name):
    """A2L CHARACTERISTIC -> table dict for the XDF writer. Raises KeyError / Unsupported / ValueError."""
    name, ch = a2l.find(name)
    items = a2l.record_layouts.get(ch['layout'])
    if items is None:
        raise Unsupported('record layout %s missing' % ch['layout'])
    kinds = {i['kind']: i for i in items}
    fnc = kinds.get('FNC_VALUES')
    if fnc is None:
        raise Unsupported('no FNC_VALUES in %s' % ch['layout'])
    if DTYPES[fnc['dtype']][0] == 8:
        raise Unsupported('dtype %s' % fnc['dtype'])
    eq, unit, dec = a2l.compu(ch['conv'])
    t = {'desc': ch['desc'], 'dtype': fnc['dtype'], 'eq': eq, 'unit': ch['phys_unit'] or unit,
         'dec': dec, 'lower': ch['lower'], 'upper': ch['upper'],
         'x': None, 'y': None, 'rows': 1, 'cols': 1, 'colmajor': False}
    addr, typ = ch['address'], ch['type']

    if typ == 'VALUE':
        t['address'] = addr + _layout_offsets(a2l, items, {})['FNC_VALUES']
        return t
    if typ == 'VAL_BLK':
        dims = [d for d in ch['matrix_dim'] if d > 1] or ([1] if ch['matrix_dim'] else [ch['number'] or 1])
        if len(dims) > 2:
            raise Unsupported('VAL_BLK >2D')
        t['cols'], t['rows'] = dims[0], (dims[1] if len(dims) > 1 else 1)
        t['address'] = addr + _layout_offsets(a2l, items, {'FNC': t['cols'] * t['rows']})['FNC_VALUES']
        return t
    if typ not in ('CURVE', 'MAP'):
        raise Unsupported(typ)

    counts, inline = {}, {}
    for letter, ax in zip('XY', ch['axes']):
        attr = ax['attr']
        if attr == 'STD_AXIS':
            n = _stored_count(a2l, b, addr, items, kinds, letter, ax['max_points'],
                              {'X': counts.get('X', 0), 'Y': 0, 'FNC': 0})
            fix = kinds.get('FIX_NO_AXIS_PTS_' + letter)
            counts[letter] = fix['n'] if fix else n
            inline[letter] = ax
            continue
        if attr in ('COM_AXIS', 'RES_AXIS'):
            ap = a2l.axis_pts.get(ax['ref'])
            if ap is None:
                raise Unsupported('missing AXIS_PTS %s' % ax['ref'])
            a = _com_axis(a2l, b, ap)
        elif attr == 'FIX_AXIS':
            a = _fix_axis(a2l, ax)
        else:
            raise Unsupported(attr)
        counts[letter] = a['count']
        t[letter.lower()] = a

    nx, ny = counts.get('X', 1), counts.get('Y', 1)
    counts['FNC'] = nx * ny
    offs = _layout_offsets(a2l, items, counts)
    for letter, ax in inline.items():
        pts = kinds.get('AXIS_PTS_' + letter)
        if pts is None:
            raise Unsupported('STD_AXIS without AXIS_PTS_%s' % letter)
        t[letter.lower()] = _addr_axis(addr + offs['AXIS_PTS_' + letter], pts['dtype'], counts[letter],
                                       a2l.compu(ax['conv']), ax['phys_unit'], ax['input'])
    t['address'] = addr + offs['FNC_VALUES']
    t['cols'], t['rows'] = nx, ny  # XDF: columns = X axis, rows = Y axis
    # ASAM COLUMN_DIR stores each X column (all Y values) contiguously -> TunerPro column-major
    t['colmajor'] = fnc['dir'] == 'COLUMN_DIR' and ny > 1
    return t


# ============================================================================
# Writing XDFs
# ============================================================================

def esc(s):
    return html.escape(str(s), quote=True)


def _typeflags(dtype, colmajor=False):
    """TunerPro mmedtypeflags: 0x1 signed, 0x2 LSB first (TriCore), 0x4 column-major, 0x10000 float."""
    size, signed, flt = DTYPES[dtype]
    return (0x02 | (signed and not flt) | (0x04 if colmajor else 0) | (0x10000 if flt else 0)), size * 8


def _dec(d):
    return 2 if d is None else max(0, min(d, 6))


def _math(eq):
    return '      <MATH equation="%s">\n        <VAR id="X" />\n      </MATH>\n' % esc(eq)


def _cats(cats):
    return ''.join('    <CATEGORYMEM index="%d" category="%d" />\n' % (i, c) for i, c in enumerate(cats))


def _axis_xml(letter, ax, count, b):
    """x/y axis: read from the bin ('addr'), fixed labels ('labels'), or plain 0..n-1 (None)."""
    if ax is not None and ax['kind'] == 'addr':
        fl, bits = _typeflags(ax['dtype'])
        emb = ('mmedtypeflags="0x%X" mmedaddress="0x%X" mmedelementsizebits="%d" mmedcolcount="%d" '
               % (fl, b.off(ax['address']), bits, ax['count']))
        units, count, dec, eq = esc(ax['unit'] or '-'), ax['count'], _dec(ax['dec']), ax['eq']
        extra, labels = '      <embedinfo type="1" />\n', []
    else:
        emb, extra, eq = 'mmedelementsizebits="8" ', '', 'X'
        if ax is None:
            units, dec, labels = '-', -1, ['%d' % i for i in range(count)]
        else:
            units, count, dec = esc(ax['unit'] or '-'), ax['count'], _dec(ax['dec'])
            labels = [esc(v) if isinstance(v, str) else _f(round(v, 6)) for v in ax['labels']]
    return ('    <XDFAXIS id="%s" uniqueid="0x0">\n'
            '      <EMBEDDEDDATA %smmedmajorstridebits="0" mmedminorstridebits="0" />\n'
            '      <units>%s</units>\n      <indexcount>%d</indexcount>\n      <decimalpl>%d</decimalpl>\n'
            '      <datatype>0</datatype>\n      <unittype>0</unittype>\n%s      <DALINK index="0" />\n%s%s'
            '    </XDFAXIS>\n'
            % (letter, emb, units, count, dec, extra,
               ''.join('      <LABEL index="%d" value="%s" />\n' % (i, v) for i, v in enumerate(labels)),
               _math(eq)))


def _z_xml(dtype, colmajor, address, rows, cols, unit, dec, minmax, eq, b):
    fl, bits = _typeflags(dtype, colmajor)
    return ('    <XDFAXIS id="z">\n'
            '      <EMBEDDEDDATA mmedtypeflags="0x%X" mmedaddress="0x%X" mmedelementsizebits="%d" '
            'mmedrowcount="%d" mmedcolcount="%d" mmedmajorstridebits="0" mmedminorstridebits="0" />\n'
            '      <units>%s</units>\n      <decimalpl>%d</decimalpl>\n%s      <outputtype>1</outputtype>\n'
            '%s    </XDFAXIS>\n'
            % (fl, b.off(address), bits, rows, cols, esc(unit or '-'), _dec(dec), minmax, _math(eq)))


def table_xml(t, title, desc, cats, b):
    minmax = ''.join('      <%s>%s</%s>\n' % (tag, _f(v), tag)
                     for tag, v in (('min', t['lower']), ('max', t['upper']))
                     if isinstance(v, (int, float)) and abs(v) < 1e30)
    return ('  <XDFTABLE uniqueid="0x0" flags="0x0">\n    <title>%s</title>\n%s%s%s%s%s  </XDFTABLE>\n'
            % (esc(title), '    <description>%s</description>\n' % esc(desc) if desc else '', _cats(cats),
               _axis_xml('x', t['x'], t['cols'], b), _axis_xml('y', t['y'], t['rows'], b),
               _z_xml(t['dtype'], t['colmajor'], t['address'], t['rows'], t['cols'], t['unit'], t['dec'],
                      minmax, t['eq'], b)))


def axis_table_xml(ax, title, cats, b):
    """1-D breakpoint table for an axis stored in the bin, like the S58 '(autogen)' tables."""
    return ('  <XDFTABLE uniqueid="0x0" flags="0x0">\n    <title>%s</title>\n'
            '    <description>%s</description>\n%s%s%s%s  </XDFTABLE>\n'
            % (esc(title), esc(ax['name']), _cats(cats),
               _axis_xml('x', None, ax['count'], b), _axis_xml('y', None, 1, b),
               _z_xml(ax['dtype'], False, ax['address'], 1, ax['count'], ax['unit'], ax['dec'], '', ax['eq'], b)))


def plain_table(address, dtype, n, unit='-', eq='X', row_labels=None):
    """A table dict for raw data with no A2L behind it: n values in a row, or one per labelled row."""
    rows, cols = (n, 1) if row_labels else (1, n)
    y = {'kind': 'labels', 'labels': row_labels, 'count': n, 'unit': '-', 'dec': 0} if row_labels else None
    return {'dtype': dtype, 'eq': eq, 'unit': unit, 'dec': 0, 'lower': None, 'upper': None,
            'x': None, 'y': y, 'rows': rows, 'cols': cols, 'colmajor': False, 'address': address}


# ============================================================================
# Fault arrays
# ============================================================================

# Bosch DSM keeps per-fault settings in arrays indexed by fault number; the A2L names each entry
# <array>.DFC_<fault>_C. [0] / [1] are the master and slave DME.
FAULT_ARRAYS = {'DFC_CtlMsk2': 'control mask', 'DFC_DisblMsk2': 'disable mask',
                'DFES_Cls': 'error class', 'DFES_DTCM': 'fault code'}
FAULT_ENTRY_RE = re.compile(r'(%s)(?:\[(\d)\])?\.DFC_(\w+)_C$' % '|'.join(FAULT_ARRAYS))
FAULT_ARRAY_RE = re.compile(r'(%s)(?:\[\d\])?$' % '|'.join(FAULT_ARRAYS))
FAULT_CATEGORY = 'Fault codes: all faults (by index)'
UINT = {1: 'UBYTE', 2: 'UWORD', 4: 'ULONG'}

FaultArray = collections.namedtuple('FaultArray', 'base size names')  # base: bin offset


def fault_arrays(a2l, b):
    """{'DFES_Cls[0]': FaultArray, ...} for every fault array laid out contiguously in fault order."""
    entries = collections.defaultdict(list)
    for name, ch in a2l.characteristics.items():
        m = FAULT_ENTRY_RE.match(name)
        if m and ch['type'] == 'VALUE':
            t = resolve(a2l, b, name)
            array = m.group(1) + ('[%s]' % m.group(2) if m.group(2) else '')
            entries[array].append((b.off(t['address']), DTYPES[t['dtype']][0], m.group(3)))
    out = {}
    for array, v in entries.items():
        v.sort()
        base, size = v[0][:2]
        if all(off == base + i * size for i, (off, _, _) in enumerate(v)):
            out[array] = FaultArray(base, size, [n for _, _, n in v])
    return out


def fault_title(array):
    m = re.match(r'(\w+)(?:\[(\d)\])?$', array)
    side = {'0': ' (master)', '1': ' (slave)'}.get(m.group(2), '')
    return 'All faults: %s%s' % (FAULT_ARRAYS[m.group(1)], side)


def fault_array_xml(array, base, size, row_labels, cat, b):
    """One table holding a whole fault array, a row per fault. The description starts with the
    array name - port and transfer recognise the table by it."""
    t = plain_table(b.base + base, UINT[size], len(row_labels), row_labels=row_labels)
    desc = ('%s - one row per fault, labelled <name> <fault code>. Raw values; the A2L does not document '
            'the bits.' % array)
    return table_xml(t, fault_title(array), desc, [cat], b)


def fault_labels(arrays, data):
    """'<name> <code>' per fault index, the code read from DFES_DTCM[0]. The name comes first:
    it identifies the fault across versions, the code can differ between cars."""
    names = next(iter(arrays.values())).names
    codes = arrays.get('DFES_DTCM[0]')
    if codes is None:
        return names
    return ['%s %X' % (n, int.from_bytes(data[codes.base + 2 * i:codes.base + 2 * i + 2], 'little'))
            for i, n in enumerate(names)]


# ============================================================================
# a2l: build an XDF from the A2L
# ============================================================================

# template categories whose tables point at MHD+ patch areas or alternate map slots
SKIP_CATEGORY_RE = re.compile(r'^(MHD\+ Suite|Map Switch|Custom Base|CANBUS|MHD Error|Custom Safeties)', re.I)

Wanted = collections.namedtuple('Wanted', 'label title desc cats source')


class Categories(dict):
    """{category id: name}; ids are what CATEGORYMEM uses (XDF index + 1)."""

    def id(self, name, preferred=None):
        for k, v in self.items():
            if v == name:
                return k
        k = preferred if preferred is not None and preferred not in self else max(self, default=0) + 1
        self[k] = name
        return k


def select_tables(templates, names_files, report):
    """-> (Categories, [Wanted]). The first table seen for a label wins."""
    cats, wanted, seen = Categories(), [], set()

    def add(w):
        if w.label.lower() in seen:
            report['dup'].append('%s  [%s, %s]' % (w.title, w.label, w.source))
        else:
            seen.add(w.label.lower())
            wanted.append(w)

    for path in templates:
        tcats, tables = load_xdf(path)
        src = os.path.basename(path)
        remap = {c: cats.id(n, c) for c, n in tcats.items()}
        for t in tables:
            if any(SKIP_CATEGORY_RE.match(tcats.get(c, '')) for c in t.cats):
                report['skipped_mhd'].append('%s  (%s)' % (t.title, src))
            elif t.row_labels and FAULT_ARRAY_RE.match(t.label):
                continue  # whole-fault-array table: --fault-arrays rebuilds it
            elif not LABEL_RE.match(t.desc):
                report['missing'].append('%s  [no label in description, %s]' % (t.title, src))
            else:
                add(Wanted(LABEL_RE.match(t.desc).group(1), t.title, t.desc, [remap.get(c, c) for c in t.cats], src))

    for path in names_files:
        with open(path, encoding='utf-8') as f:
            for line in f:
                if line.strip() and not line.lstrip().startswith('#'):
                    label, title, cat = ([p.strip() for p in line.rstrip('\n').split('\t')] + ['', ''])[:3]
                    add(Wanted(label, title or label, None, [cats.id(cat or 'Uncategorized')], 'names'))
    return cats, wanted


def xdf_document(description, size, cats, body):
    return ('<?xml version="1.0" encoding="utf-8"?>\n'
            '<XDFFORMAT xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" '
            'xmlns:xsd="http://www.w3.org/2001/XMLSchema" version="1.80">\n'
            '  <XDFHEADER>\n    <flags>0x1</flags>\n'
            '    <description>%s</description>\n'
            '    <BASEOFFSET offset="0" subtract="0" />\n'
            '    <DEFAULTS datasizeinbits="16" sigdigits="1" outputtype="1" signed="0" lsbfirst="1" float="0" />\n'
            '    <REGION type="0xFFFFFFFF" startaddress="0x0" size="0x%X" regioncolor="0x0" regionflags="0x0" '
            'name="Binary File" desc="This region describes the bin file edited by this XDF" />\n%s'
            '  </XDFHEADER>\n%s</XDFFORMAT>\n'
            % (esc(description), size,
               ''.join('    <CATEGORY index="0x%X" name="%s" />\n' % (k - 1, esc(v)) for k, v in cats.items()),
               ''.join(body)))


def cmd_a2l(args):
    """
    Build an XDF from an A2L and a flash read of the same software. Tables come from:
      --template X.xdf  (repeatable) an existing XDF: every table whose description starts with an
                        A2L label is rebuilt from the A2L (address, type, scaling, axes), keeping
                        the template's title, description and categories. MHD+ patch tables are
                        skipped; earlier templates win on duplicate labels. Every XDF this tool
                        writes works as a template, so a newer S68 A2L only needs
                        --template S68/<SWFL>/<SWFL>.xdf --fault-arrays.
      --names FILE      (repeatable) one A2L label per line: LABEL[<TAB>Title[<TAB>Category]]
      --fault-arrays    one table per Bosch fault array (disable mask, error class, ...) with a
                        row per fault, labelled with its name and code
    """
    print('loading A2L ...', file=sys.stderr)
    a2l = A2L.load(args.a2l, cache=not args.no_cache)
    b = Bin(args.bin, int(args.base, 0))
    print('  %d characteristics, %d axis_pts, %d compu methods'
          % (len(a2l.characteristics), len(a2l.axis_pts), len(a2l.compu_methods)), file=sys.stderr)

    report = {'missing': [], 'unsupported': [], 'skipped_mhd': [], 'dup': []}
    cats, wanted = select_tables(args.template, args.names, report)
    by_name = {v: k for k, v in cats.items()}

    def bp_cats(ids):
        """'<category> breakpoints' for each category, if the XDF has one."""
        return [by_name.get(cats[c] + ' breakpoints', c) for c in ids if c in cats] or ids

    body, used, axes_done = [], set(), set()
    for w in wanted:
        try:
            t = resolve(a2l, b, w.label)
        except KeyError:
            report['missing'].append('%s  [%s, %s]' % (w.title, w.label, w.source))
            continue
        except (Unsupported, ValueError) as e:
            report['unsupported'].append('%s  [%s]: %s' % (w.title, w.label, e))
            continue
        desc = w.desc or ('%s - %s' % (w.label, t['desc']) if t['desc'] else w.label)
        body.append(table_xml(t, w.title, desc, w.cats, b))
        used.update(w.cats)
        for letter in ('x', 'y'):
            ax = t[letter]
            if args.no_axis_tables or not ax or ax['kind'] != 'addr' or (ax['address'], ax['count']) in axes_done:
                continue
            axes_done.add((ax['address'], ax['count']))
            body.append(axis_table_xml(ax, '%s %s (autogen)' % (w.title, letter.upper()), bp_cats(w.cats), b))
            used.update(bp_cats(w.cats))
    n_tables = len(body) - len(axes_done)

    if args.fault_arrays:
        arrays = fault_arrays(a2l, b)
        labels = fault_labels(arrays, b.data)
        cat = cats.id(FAULT_CATEGORY)
        used.add(cat)
        body += [fault_array_xml(name, fa.base, fa.size, labels, cat, b) for name, fa in sorted(arrays.items())]
        print('  fault arrays: %d tables of %d faults' % (len(arrays), len(labels)), file=sys.stderr)

    cats = Categories((k, v) for k, v in cats.items() if k in used)
    with open(args.output, 'w', encoding='utf-8', newline='\r\n') as f:
        f.write(xdf_document(args.description or 'Generated by tools/xdftool.py from %s' % a2l.project,
                             len(b.data), cats, body))

    report['unscaled'] = sorted(a2l.unscaled)
    print('wrote %s: %d tables (+%d axis tables)' % (args.output, n_tables, len(axes_done)), file=sys.stderr)
    print('  missing in A2L: %d, unsupported: %d, MHD+-only skipped: %d, duplicate labels: %d, '
          'raw values (scaling not converted): %d'
          % tuple(len(report[k]) for k in ('missing', 'unsupported', 'skipped_mhd', 'dup', 'unscaled')),
          file=sys.stderr)
    if args.report:
        headings = {'missing': 'Missing in A2L', 'unsupported': 'Unsupported',
                    'skipped_mhd': 'Skipped MHD+-only template tables', 'dup': 'Duplicate labels',
                    'unscaled': 'COMPU_METHODs left as raw values'}
        with open(args.report, 'w', encoding='utf-8') as f:
            f.write('# xdftool a2l report\n')
            for key, heading in headings.items():
                f.write('\n## %s (%d)\n' % (heading, len(report[key])))
                f.writelines('- %s\n' % row for row in report[key])


# ============================================================================
# port: move an XDF to another software version
# ============================================================================

WINDOW = 0x4000          # how far a table may move between versions
MIN_PATTERN = 12         # bytes; shorter patterns match too often
W, STRIDE = 16, 2        # byte-window anchors: window size and step
NEAR = 256               # anchors this close to a table are its candidate shifts
CTX = 12                 # bytes of neighbouring context used when a table's values changed

TABLE_RE = re.compile(r'  <XDFTABLE\b.*?</XDFTABLE>\r?\n', re.S)
ADDR_RE = re.compile(r'mmedaddress="(0x[0-9A-Fa-f]+)"')


def unique_hit(dst, pat, center):
    lo = max(0, center - WINDOW)
    hits = [m.start() + lo for m in re.finditer(re.escape(pat), dst[lo:center + WINDOW + len(pat)])]
    return hits[0] if len(hits) == 1 else None


class Anchors:
    """{src offset: shift} from unique byte runs, and the shift they imply for any address."""

    def __init__(self, src, dst, spans, region):
        self.src, self.dst = src, dst
        lo, hi = region
        index = {}
        for i in range(max(0, lo - WINDOW), min(len(dst), hi + WINDOW) - W):
            index.setdefault(dst[i:i + W], []).append(i)
        found = {}
        for i in range(lo, hi - W, STRIDE):  # every distinctive 16-byte window
            win = src[i:i + W]
            if len(set(win)) >= 5:
                hits = [h for h in index.get(win, ()) if abs(h - i) <= WINDOW]
                if len(hits) == 1:
                    found[i] = hits[0] - i
        for a, b in spans:  # table headers / records, which may be longer
            pat = src[a:b]
            if len(pat) >= MIN_PATTERN and len(set(pat)) >= 4:
                hit = unique_hit(dst, pat, a)
                if hit is not None:
                    found[a] = hit - a
        self.shifts = {}
        run = []  # keep anchors in runs of at least 3 consecutive ones with the same shift
        for k in sorted(found) + [None]:
            if run and (k is None or found[k] != found[run[0]]):
                if len(run) >= 3:
                    self.shifts.update((r, found[r]) for r in run)
                run = []
            if k is not None:
                run.append(k)
        self.keys = sorted(self.shifts)

    def add(self, more):
        self.shifts.update(more)
        self.keys = sorted(self.shifts)

    def shift(self, addr, size):
        """-> (shift, 'same' | 'verified' | 'guessed')"""
        keys, shifts, src, dst = self.keys, self.shifts, self.src, self.dst
        i = bisect.bisect_right(keys, addr)
        below = keys[i - 1] if i else None
        above = keys[i] if i < len(keys) else None
        if below is None or above is None or shifts[below] == shifts[above]:
            return shifts[below if below is not None else above], 'same'
        near = set(keys[bisect.bisect_left(keys, addr - NEAR):bisect.bisect_right(keys, addr + size + NEAR)])
        near = sorted(near | {below, above}, key=lambda k: min(abs(k - addr), abs(k - addr - size)))
        cands = list(dict.fromkeys(shifts[k] for k in near))
        # the table's own bytes, else the bytes right before / after it (when its values changed)
        for lo, hi in ((addr, addr + size), (addr - CTX, addr), (addr + size, addr + size + CTX)):
            pat = src[lo:hi]
            if len(set(pat)) >= 3:  # filler bytes prove nothing
                ok = [d for d in cands if dst[lo + d:hi + d] == pat]
                if len(ok) == 1 or (ok and lo == addr):
                    return ok[0], 'verified'
        return cands[0], 'guessed'


def a2l_spans(a2l, b):
    """Header+axes (or whole record) byte spans of every A2L CURVE/MAP/VAL_BLK."""
    spans = []
    for name, ch in a2l.characteristics.items():
        if ch['type'] not in ('CURVE', 'MAP', 'VAL_BLK'):
            continue
        try:
            t = resolve(a2l, b, name)
        except (Unsupported, ValueError, KeyError):
            continue
        lo, fnc = b.off(ch['address']), b.off(t['address'])
        end = fnc + t['rows'] * t['cols'] * DTYPES[t['dtype']][0]
        spans.append((lo, fnc if fnc - lo >= MIN_PATTERN else end))
    return spans


class FaultMap:
    """
    New software versions insert and remove faults, and every fault array grows or shrinks by the
    same entries. The fault-code arrays (DFES_DTCM) give a first index mapping; each array's new
    base is where the most stock values agree; then the mapping is redone on every array's stock
    value per fault, since many faults share a code and a code-only alignment slips inside runs
    of equal codes.
        .bases {array: new base}   .index {old fault index: new index}   .count  new fault count
    """

    def __init__(self, arrays, src, dst, anchors):
        self.arrays, self.src, self.dst, self.anchors = arrays, src, dst, anchors
        self.bases, self.index, self.count = {}, {}, 0
        d0, d1 = arrays.get('DFES_DTCM[0]'), arrays.get('DFES_DTCM[1]')
        if not (d0 and d1):
            return
        h0, h1 = (unique_hit(dst, src[a.base:a.base + 48], a.base) for a in (d0, d1))
        if h0 is None or h1 is None or h1 <= h0:
            return
        self.count = (h1 - h0) // d0.size
        self.bases = {'DFES_DTCM[0]': h0}
        self.align(fill=False)
        self.bases = self.find_bases()
        for _ in range(2):
            self.align(fill=True)
            self.bases = self.find_bases(self.bases)

    @property
    def names(self):
        return next(iter(self.arrays.values())).names

    def entry(self, data, name, base, i):
        size = self.arrays[name].size
        return data[base + i * size:base + (i + 1) * size]

    def align(self, fill):
        """Index mapping from the longest common subsequence of per-fault signatures: the fault's
        entry in every array whose new base is known."""
        names = sorted(self.bases)
        def sigs(data, bases, n):
            return [tuple(self.entry(data, nm, bases[nm], i) for nm in names) for i in range(n)]
        sm = difflib.SequenceMatcher(None, sigs(self.src, {nm: self.arrays[nm].base for nm in names}, len(self.names)),
                                     sigs(self.dst, self.bases, self.count), autojunk=False)
        blocks = [blk for blk in sm.get_matching_blocks() if blk.size]
        self.index = {a + i: b + i for a, b, n in blocks for i in range(n)}
        if fill:  # equal-length gaps between matched runs: same faults, values differing by car/region
            for (a1, b1, n1), (a2, b2, _) in zip(blocks, blocks[1:]):
                if a2 - (a1 + n1) == b2 - (b1 + n1):
                    self.index.update({a1 + n1 + i: b1 + n1 + i for i in range(a2 - a1 - n1)})

    def find_bases(self, prev=None):
        """Each array's new base: the offset where the most sampled faults keep their stock value."""
        bases, sample = {}, list(self.index)[::7]
        for name, fa in self.arrays.items():
            if prev and name in prev:
                guess, span = prev[name], 0x40
            else:
                guess, span = fa.base + self.anchors.shift(fa.base, fa.size)[0], 0x400
            score = lambda g: sum(self.entry(self.src, name, fa.base, i) == self.entry(self.dst, name, g, self.index[i])
                                  for i in sample)
            best = max(range(guess - span, guess + span + 1), key=score)
            if score(best) >= 0.5 * len(sample):
                bases[name] = best
        return bases

    def locate(self, addr):
        """(array, new offset or None) for an address on an entry of a mapped array, else None."""
        for name, fa in self.arrays.items():
            if name in self.bases and fa.base <= addr < fa.base + fa.size * len(fa.names) \
                    and (addr - fa.base) % fa.size == 0:
                i = self.index.get((addr - fa.base) // fa.size)
                return name, (None if i is None else self.bases[name] + i * fa.size)
        return None

    def row_labels(self):
        """New-version row labels: '<old fault name> <code>' where the fault was matched, else
        'new_<index> <code>'; the code is the one the new version stores."""
        old = {j: i for i, j in self.index.items()}
        code = lambda j: int.from_bytes(self.entry(self.dst, 'DFES_DTCM[0]', self.bases['DFES_DTCM[0]'], j), 'little')
        return ['%s %X' % (self.names[old[j]] if j in old else 'new_%d' % j, code(j)) for j in range(self.count)]


def table_label(block):
    m = re.search(r'<description>(.*?)</description>', block, re.S)
    lm = LABEL_RE.match(m.group(1)) if m else None
    return lm.group(1) if lm else ''


def table_title(block):
    m = re.search(r'<title>(.*?)</title>', block, re.S)
    return html.unescape(m.group(1)) if m else '?'


def element_sizes(xdf):
    """{offset: byte length} of every EMBEDDEDDATA with an address (the longest at a shared address)."""
    out = {}
    for emb in ET.fromstring(xdf.encode('utf-8')).iter('EMBEDDEDDATA'):
        a = emb.attrib
        if 'mmedaddress' in a:
            n = int(a.get('mmedrowcount', 1)) * int(a.get('mmedcolcount', 1)) * int(a.get('mmedelementsizebits', 8)) // 8
            addr = int(a['mmedaddress'], 16)
            out[addr] = max(n, out.get(addr, 0))
    return out


def category_id(xdf, name):
    """-> (xdf, CATEGORYMEM id for name), adding the category to the header if needed."""
    found = re.search(r'<CATEGORY index="(0x[0-9A-Fa-f]+)" name="%s"' % re.escape(esc(name)), xdf)
    if found:
        return xdf, int(found.group(1), 16) + 1
    idx = max((int(i, 16) for i in re.findall(r'<CATEGORY index="(0x[0-9A-Fa-f]+)"', xdf)), default=-1) + 1
    nl = '\r\n' if '\r\n' in xdf else '\n'
    xdf = xdf.replace('  </XDFHEADER>', '    <CATEGORY index="0x%X" name="%s" />%s  </XDFHEADER>'
                      % (idx, esc(name), nl), 1)
    return xdf, idx + 1


def extra_tables(path):
    with open(path, encoding='utf-8') as f:
        for line in f:
            if line.strip() and not line.startswith('#'):
                off, dtype, n, unit, cat, title, desc = line.rstrip('\n').split('\t')
                yield int(off, 0), dtype, int(n), unit, cat, title, desc



def cmd_port(args):
    """
    Move an XDF to another software version (ASW / SWFL) of the same DME. Between versions the
    linker shifts calibration tables in blocks, so the address difference is piecewise constant.
    Anchors - byte runs found exactly once near their old place in the new read - give the shift
    for each stretch. Anchors are byte values, so the two reads should be the same car (similar
    calibration). Every address is then classified:

      same      the anchors on both sides agree on the shift
      verified  they disagree; the table's own bytes (or the bytes right before / after it, if
                its values changed) match at the chosen shift
      guessed   they disagree and the bytes don't decide; the nearest anchor's shift is used -
                check these by hand, or leave them out with --drop-guessed
      indexed   a fault-array entry, moved to its fault's index in the new version (--a2l)
      removed   a fault-array entry whose fault has no match in the new version - dropped

    Whole-fault-array tables are rebuilt for the new version, rows labelled with the old fault
    names where the fault was matched and new_<index> where not.

    --extra lines, tab separated: OFFSET  A2L_TYPE  COUNT  UNITS  CATEGORY  TITLE  DESCRIPTION
    """

    src, dst = read_bin(args.src_bin), read_bin(args.dst_bin)
    with open(args.xdf, encoding='utf-8-sig', newline='') as f:
        xdf = f.read()
    nl = '\r\n' if '\r\n' in xdf else '\n'

    arrays, spans = {}, []
    if args.a2l:
        a2l, b = A2L.load(args.a2l), Bin(args.src_bin)
        arrays, spans = fault_arrays(a2l, b), a2l_spans(a2l, b)

    # whole-fault-array tables are rebuilt at the end, not shifted
    array_tables = [m.group(0) for m in TABLE_RE.finditer(xdf) if table_label(m.group(0)) in arrays]
    for block in array_tables:
        xdf = xdf.replace(block, '', 1)

    sizes = element_sizes(xdf)
    spans += [(a, a + n) for a, n in sizes.items()]
    anchors = Anchors(src, dst, spans, (min(sizes) - 0x1000, max(a + n for a, n in sizes.items()) + 0x1000))
    print('%d anchors, %d distinct shifts' % (len(anchors.shifts), len(set(anchors.shifts.values()))), file=sys.stderr)
    status = {a: anchors.shift(a, n) for a, n in sizes.items()}

    faults = FaultMap(arrays, src, dst, anchors) if arrays else None
    if faults:
        for a in sizes:
            hit = faults.locate(a)
            if hit:
                status[a] = (0, 'removed') if hit[1] is None else (hit[1] - a, 'indexed')
        print('fault arrays: %d of %d mapped, %d of %d faults matched'
              % (len(faults.bases), len(arrays), len(faults.index), len(faults.names)), file=sys.stderr)
        if len(faults.bases) < len(arrays):
            print('WARNING: fault arrays not all located - is the source read the same car as the target?',
                  file=sys.stderr)

    for _ in range(5):  # verified tables anchor their still-guessed neighbours
        new = {a: d for a, (d, st) in status.items() if st == 'verified' and a not in anchors.shifts}
        if not new:
            break
        anchors.add(new)
        for a, (_, st) in list(status.items()):
            if st == 'guessed':
                status[a] = anchors.shift(a, sizes[a])

    drop = re.compile(args.drop) if args.drop else None
    tables = collections.defaultdict(list)  # outcome -> titles

    def keep(m):
        block, title = m.group(0), table_title(m.group(0))
        sts = {status[int(a, 16)][1] for a in ADDR_RE.findall(block)}
        if drop and drop.search(title):
            why = 'drop'
        elif 'removed' in sts:
            why = 'removed'
        elif 'guessed' in sts:
            why = 'guessed' if args.drop_guessed else 'kept guessed'
        else:
            why = 'kept'
        tables[why].append(title)
        return block if why.startswith('kept') else ''
    out = TABLE_RE.sub(keep, xdf)
    out = ADDR_RE.sub(lambda m: 'mmedaddress="0x%X"' % (int(m.group(1), 16) + status[int(m.group(1), 16)][0]), out)

    added = []
    dbin = Bin(args.dst_bin)
    if array_tables and faults and faults.bases:
        out, cat = category_id(out, FAULT_CATEGORY)
        labels = faults.row_labels()
        for name in sorted(faults.bases):
            added.append(fault_array_xml(name, faults.bases[name], arrays[name].size, labels, cat, dbin))
    for off, dtype, n, unit, cat_name, title, desc in (extra_tables(args.extra) if args.extra else ()):
        out, cat = category_id(out, cat_name)
        added.append(table_xml(plain_table(dbin.base + off, dtype, n, unit), title, desc, [cat], dbin))
    out = out.replace('</XDFFORMAT>', ''.join(added).replace('\n', nl) + '</XDFFORMAT>', 1)
    if args.description:
        out = re.sub(r'(<XDFHEADER>.*?<description>).*?(</description>)',
                     lambda m: m.group(1) + esc(args.description) + m.group(2), out, count=1, flags=re.S)

    with open(args.output, 'w', encoding='utf-8', newline='') as f:
        f.write(out)

    addrs = ', '.join('%d %s' % (sum(1 for _, s in status.values() if s == k), k)
                      for k in ('same', 'verified', 'guessed', 'indexed', 'removed'))
    headings = {'removed': 'Dropped: fault not in the new version', 'guessed': 'Dropped: guessed address',
                'drop': 'Dropped: --drop', 'kept guessed': 'Kept with a guessed address - check by hand'}
    print('addresses: %s\ntables: %d kept, %d added, %s' % (addrs, len(tables['kept']), len(added),
          ', '.join('%d %s' % (len(tables[k]), h.lower()) for k, h in headings.items())), file=sys.stderr)
    if args.report:
        with open(args.report, 'w', encoding='utf-8') as f:
            f.write('# xdftool port report\n\n%d anchors; addresses: %s\n' % (len(anchors.shifts), addrs))
            for k, heading in headings.items():
                f.write('\n## %s (%d)\n' % (heading, len(tables[k])))
                f.writelines('- %s\n' % t for t in tables[k])


# ============================================================================
# diff: what a tune changed
# ============================================================================

def compare(t, twin, stock, tune):
    """-> (cells changed, cells compared, stock values, tune values, note), or None if unchanged."""
    if t.row_labels:  # fault array: rows with the same label
        cells, other = t.cells(), twin.cells()
        val = lambda data, cell: int.from_bytes(data[cell[0]:cell[0] + cell[1]], 'little')
        rows = [k for k in cells if k in other and other[k][1] == cells[k][1]]
        changed = [k for k in rows if val(stock, cells[k]) != val(tune, other[k])]
        if not changed:
            return None
        a = [val(stock, cells[k]) for k in changed]
        b = [val(tune, other[k]) for k in changed]
        return len(changed), len(rows), a, b, 'rows: ' + ', '.join(changed)
    if [e.size for e in t.elements] != [e.size for e in twin.elements]:
        return 0, 0, [], [], 'different shape in the tune XDF'
    raw = [(e.raw(stock), f.raw(tune)) for e, f in zip(t.elements, twin.elements)]
    if all(x == y for x, y in raw):
        return None
    a, b = t.z.phys(stock), twin.z.phys(tune)
    axes = [e.role for e, (x, y) in zip(t.elements, raw) if e.role != 'z' and x != y]
    return (sum(abs(x - y) > 1e-9 for x, y in zip(a, b)), len(a), a, b,
            'axes changed: %s' % ','.join(axes) if axes else '')


def byte_runs(offsets, gap=4):
    runs = []
    for i in offsets:
        if runs and i - runs[-1][1] <= gap:
            runs[-1][1] = i
        else:
            runs.append([i, i])
    return runs


def cmd_diff(args):
    """
    What changed between a stock read and a tuned read, through an XDF: every table whose values
    differ, with stock and tuned values. On the same software it also lists changed bytes no
    table covers and the share of changed bytes inside a table (calibration area unless --region).

    With --tune-xdf the tune may be on another software version, e.g. a tune whose own stock read
    is missing, against a stock read of the same car. Tables pair up by A2L label (else title),
    fault arrays row by row; differences then include calibration changes between the versions.
    """

    stock, tune = read_bin(args.stock), read_bin(args.tune)
    cats, tables = load_xdf(args.xdf)
    tune_tables = load_xdf(args.tune_xdf)[1] if args.tune_xdf else tables

    changed, unpaired = [], []
    for t, twin in pair_tables(tables, tune_tables):
        if twin is None:
            unpaired.append(t)
            continue
        res = compare(t, twin, stock, tune)
        if res:
            changed.append((category(cats, t), t, res))

    out = ['# xdftool diff report\n\n']
    out.append(''.join('- %s: `%s` (%s)\n' % (k, os.path.basename(p), software_id(d))
                       for k, p, d in (('stock', args.stock, stock), ('tune', args.tune, tune))))
    out.append('- xdf: `%s`%s\n' % (os.path.basename(args.xdf),
                                    ', tune xdf: `%s`' % os.path.basename(args.tune_xdf) if args.tune_xdf else ''))
    summary = 'tables changed %d of %d' % (len(changed), len(tables))
    runs = []
    if not args.tune_xdf:
        lo, hi = (0, None) if args.region == 'all' else (int(x, 0) for x in args.region.split(':'))
        diff = diff_offsets(stock, tune, lo, hi)
        covered = {i for t in tables for e in t.elements for i in range(e.address, e.address + e.size)}
        unmapped = [i for i in diff if i not in covered]
        runs = byte_runs(unmapped)
        pct = 100.0 * (len(diff) - len(unmapped)) / len(diff) if diff else 100.0
        out.append('- changed bytes: **%d** (%.3f%% of the file)\n' % (len(diff), 100.0 * len(diff) / len(stock)))
        out.append('- inside an XDF table: **%d (%.2f%%)**, outside: %d bytes in %d runs\n'
                   % (len(diff) - len(unmapped), pct, len(unmapped), len(runs)))
        summary = 'changed bytes %d | in XDF tables %.2f%% | %s | unmapped runs %d' % (len(diff), pct, summary, len(runs))
    else:
        out.append('- tables not in the tune XDF: %d\n' % len(unpaired))
    out.append('- XDF tables changed: **%d** of %d\n' % (len(changed), len(tables)))

    out.append('\n## Changed tables\n\n| Category | Table | Cells changed | Stock | Tune | Units | Note |\n'
               '|---|---|---|---|---|---|---|\n')
    show = (lambda v: ' '.join('%g' % x for x in v)) if args.all_values else fmt_range
    for cat, t, (n, total, a, b, note) in sorted(changed, key=lambda r: (r[0], r[1].title)):
        if not args.all_values and len(note) > 200:
            note = note[:200] + ' ...'
        out.append('| %s | %s | %d/%d | %s | %s | %s | %s |\n'
                   % (cat, t.title.replace('|', '/'), n, total, show(a), show(b), t.units, note))
    if args.tune_xdf:
        out.append('\n## Tables not in the tune XDF (%d)\n\n' % len(unpaired))
        out.extend('- %s\n' % t.title for t in unpaired)
    else:
        out.append('\n## Changed bytes outside every XDF table (%d runs)\n\n' % len(runs))
        out.extend('- 0x%06X +%d: stock `%s` tune `%s`\n' % (s, e - s + 1, stock[s:e + 1].hex(' '), tune[s:e + 1].hex(' '))
                   for s, e in runs)

    text = ''.join(out)
    if args.report:
        with open(args.report, 'w', encoding='utf-8') as f:
            f.write(text)
    else:
        print(text)
    print(summary, file=sys.stderr)


# ============================================================================
# transfer: copy a tune onto another car
# ============================================================================

ORDER = ('skipped', 'partial', 'moved', 'exact', 'excluded')


def transfer(t, twin, ss, st, ds, out, no_moved):
    """Copy table t's tuned cells into out -> (grade, note, src offsets written)."""
    changed = {k: c for k, c in t.cells().items() if ss[c[0]:c[0] + c[1]] != st[c[0]:c[0] + c[1]]}
    if twin is None:
        return 'skipped', 'not in the customer XDF', set()
    dst = twin.cells()
    if not t.row_labels and [n for _, n in t.cells().values()] != [n for _, n in dst.values()]:
        return 'skipped', 'different shape in the customer XDF', set()
    pairs = [(a, dst[k][0], n) for k, (a, n) in changed.items() if k in dst and dst[k][1] == n]
    missing = len(changed) - len(pairs)
    if not pairs:
        return 'skipped', 'none of the changed rows exist in the customer software', set()
    # stock comparison: every cell of an ordinary table (axes included), only the written rows of a fault array
    compared = pairs if t.row_labels else [(a, dst[k][0], n) for k, (a, n) in t.cells().items()]
    moved = any(ds[d:d + n] != ss[a:a + n] for a, d, n in compared)
    if moved and no_moved:
        return 'skipped', 'customer stock differs (--no-moved)', set()
    for a, d, n in pairs:
        out[d:d + n] = st[a:a + n]
    done = {i for a, _, n in pairs for i in range(a, a + n)}
    if missing:
        return 'partial', '%d of %d changed rows not in the customer software' % (missing, len(changed)), done
    return ('moved' if moved else 'exact'), ('%d rows' % len(pairs) if t.row_labels else ''), done


def cmd_transfer(args):
    """
    Copy a tune's XDF-table changes onto another car's stock read, on any software version.
    --xdf, --src-stock and --src-tune share one software version; when the customer's differs,
    --dst-xdf is its XDF (from `port`). Tables pair up by A2L label (else title), fault arrays row
    by row by fault name. Every table the tune changed is graded:

      exact     the customer's stock bytes equal the source stock -> tuned bytes copied
      moved     the customer's stock values differ (other car / calibration); tuned bytes copied
                anyway since a tune sets absolute values - review these (--no-moved skips them)
      partial   fault-array rows the customer's software doesn't have were left out
      skipped   no matching table, or a different shape -> nothing written

    Only bytes inside XDF tables are carried over; other edits are counted, never copied.
    Checksums / signature are NOT corrected - the flashing tool must do that.
    """

    ss, st, ds = (read_bin(p) for p in (args.src_stock, args.src_tune, args.dst_stock))
    if len(ss) != len(st):
        sys.exit('source stock and tune differ in size')
    if software_id(ss) != software_id(ds) and not args.dst_xdf:
        sys.exit('customer software %s differs from %s: pass --dst-xdf (xdftool.py port makes one)'
                 % (software_id(ds), software_id(ss)))
    cats, tables = load_xdf(args.xdf)
    dst_tables = load_xdf(args.dst_xdf)[1] if args.dst_xdf else tables
    exclude = re.compile(args.exclude) if args.exclude else None

    out, rows, written, in_tables = bytearray(ds), [], set(), set()
    for t, twin in pair_tables(tables, dst_tables):
        if all(ss[e.address:e.address + e.size] == st[e.address:e.address + e.size] for e in t.elements):
            continue
        in_tables.update(i for e in t.elements for i in range(e.address, e.address + e.size))
        cat = category(cats, t)
        if exclude and (exclude.search(t.title) or exclude.search(cat)):
            rows.append(('excluded', cat, t, '', '', ''))
            continue
        grade, note, done = transfer(t, twin, ss, st, ds, out, args.no_moved)
        written |= done
        before = fmt_range(twin.z.phys(ds)) if twin and grade != 'skipped' and not t.row_labels else ''
        after = fmt_range(t.z.phys(st)) if not t.row_labels else ''
        rows.append((grade, cat, t, before, after, note))

    with open(args.output, 'wb') as f:
        f.write(out)

    tuned = set(diff_offsets(ss, st))
    count = {g: sum(1 for r in rows if r[0] == g) for g in ORDER}
    carried = len(tuned & written)
    summary = ('customer software %s, tune from %s\n'
               'tables changed by the tune: %d | %s\n'
               'tuned bytes: %d | carried over: %d (%.1f%%) | in skipped tables or rows: %d | outside every XDF table: %d\n'
               'checksums NOT corrected'
               % (software_id(ds), software_id(ss), len(rows), ' | '.join('%s %d' % kv for kv in count.items()),
                  len(tuned), carried, 100.0 * carried / len(tuned) if tuned else 100,
                  len(tuned & in_tables) - carried, len(tuned - in_tables)))
    print(summary, file=sys.stderr)
    if args.report:
        with open(args.report, 'w', encoding='utf-8') as f:
            f.write('# xdftool transfer report\n\n```\n%s\n```\n\n| Grade | Category | Table | Customer stock | Written | Note |\n'
                    '|---|---|---|---|---|---|\n' % summary)
            for g, cat, t, before, after, note in sorted(rows, key=lambda r: (ORDER.index(r[0]), r[1], r[2].title)):
                f.write('| %s | %s | %s | %s | %s | %s |\n' % (g, cat, t.title.replace('|', '/'), before, after, note))


# ============================================================================
# xdf2a2l: export an XDF as a reduced A2L
# ============================================================================

A2L_NAME_RE = re.compile(r'^[A-Za-z_][A-Za-z0-9_.\[\]]*$')
_NUM = r'-?\d+(?:\.\d+)?(?:e-?\d+)?'
LIN_EQ_RE = re.compile(r'^X(?:\*(%s))?(?:([+-])(%s))?$' % (_NUM, _NUM))
RAT_EQ_RE = re.compile(r'^\((%s)-(%s)\*X\)/\((%s)\*X-(%s)\)$' % ((_NUM,) * 4))
DTYPE_OF = {(1, False): 'UBYTE', (1, True): 'SBYTE', (2, False): 'UWORD', (2, True): 'SWORD',
            (4, False): 'ULONG', (4, True): 'SLONG', (8, False): 'A_UINT64', (8, True): 'A_INT64'}


def rat_func(eq):
    """A TunerPro equation (raw -> physical) as A2L RAT_FUNC coefficients (physical -> raw): the
    exact inverse of A2L.compu(), so equations survive the round trip as written."""
    eq = eq.replace(' ', '')
    m = LIN_EQ_RE.match(eq)
    if m:
        a, b = float(m.group(1) or 1), float(m.group(3) or 0) * (-1 if m.group(2) == '-' else 1)
        return 0, 1, -b, 0, 0, a
    m = RAT_EQ_RE.match(eq)
    if m:
        c, f, e, b = map(float, m.groups())
        return 0, b, c, 0, e, f
    y0, y1 = evaluate(eq, 0), evaluate(eq, 1)  # anything else: assume linear and fit it
    return 0, 1, -y0, 0, 0, y1 - y0


def _a2l_str(s):
    return '"%s"' % ' '.join(str(s).replace('"', "'").split())


def _xdf_axis(ax):
    """An XDFAXIS -> ('addr', element, eq, unit, dec) | ('labels', [values], unit, dec) | ('plain',)."""
    emb, labels = ax.find('EMBEDDEDDATA'), [lab.get('value', '') for lab in ax.findall('LABEL')]
    math = ax.find('MATH')
    eq = math.get('equation', 'X') if math is not None else 'X'
    unit, dec = ax.findtext('units') or '-', int(ax.findtext('decimalpl') or 2)
    if emb is not None and 'mmedaddress' in emb.attrib:
        return 'addr', Element(ax.get('id'), emb.attrib, eq, int(ax.findtext('indexcount') or 0) or None), eq, unit, dec
    if dec == -1 and labels == [str(i) for i in range(len(labels))]:
        return ('plain',)
    return 'labels', labels, unit, dec


def _xdf_axis_names(tables):
    """{axis offset: A2L name}: an '(autogen)' breakpoint table's description names its axis."""
    names = {}
    for tbl in tables:
        if (tbl.findtext('title') or '').endswith('(autogen)'):
            emb = tbl.find("XDFAXIS[@id='z']/EMBEDDEDDATA")
            names.setdefault(int(emb.get('mmedaddress'), 16), (tbl.findtext('description') or '').strip())
    return names


def _xdf_category(tbl, cats):
    return next((cats[int(c.get('category'))] for c in tbl.findall('CATEGORYMEM') if int(c.get('category')) in cats), '')


class A2LWriter:
    """Collects A2L objects, deduplicating record layouts, conversions and axis points."""

    def __init__(self):
        self.layouts, self.compus, self.axes, self.chars, self.names = {}, {}, {}, [], set()

    def name(self, wanted):
        n, k = wanted, 1
        while n in self.names:
            k += 1
            n = '%s_%d' % (wanted, k)
        self.names.add(n)
        return n

    def std_layout(self, x, y, dtype, colmajor):
        """Record layout with the axis points stored inline before the values (STD_AXIS)."""
        axes = [(k, self.dtype(e)) for k, e in (('X', x), ('Y', y)) if e]
        items = ['AXIS_PTS_%s %d %s INDEX_INCR DIRECT' % (k, i + 1, dt) for i, (k, dt) in enumerate(axes)]
        items.append('FNC_VALUES %d %s %s DIRECT' % (len(items) + 1, dtype, 'COLUMN_DIR' if colmajor else 'ROW_DIR'))
        key = 'RL_STD_' + '_'.join(k + dt for k, dt in axes) + '_' + dtype + ('_COL' if colmajor else '')
        self.layouts[key] = ' '.join(items)
        return key

    def layout(self, kind, dtype, colmajor=False):
        if kind == 'axis':
            key = 'RL_AX_%s' % dtype
            self.layouts[key] = 'AXIS_PTS_X 1 %s INDEX_INCR DIRECT' % dtype
        else:
            key = 'RL_%s_%s' % (dtype, 'COL' if colmajor else 'ROW')
            self.layouts[key] = 'FNC_VALUES 1 %s %s DIRECT' % (dtype, 'COLUMN_DIR' if colmajor else 'ROW_DIR')
        return key

    def compu(self, eq, unit, dec):
        key = (eq, '' if unit == '-' else unit, max(0, dec))
        if key not in self.compus:
            self.compus[key] = 'CM_%d' % len(self.compus)
        return self.compus[key]

    @staticmethod
    def dtype(e):
        if e.flags & 0x10000:
            return 'FLOAT32_IEEE' if e.step == 4 else 'FLOAT64_IEEE'
        return DTYPE_OF[(e.step, bool(e.flags & 1))]

    def axis_pts(self, e, eq, unit, dec, name):
        if e.address not in self.axes:
            self.axes[e.address] = (self.name(name), e, self.compu(eq, unit, dec), self.layout('axis', self.dtype(e)))
        return self.axes[e.address][0]

    def text(self, project, description):
        out = ['ASAP2_VERSION 1 71\n/begin PROJECT %s %s\n  /begin MODULE %s ""\n' % (project, _a2l_str(description), project),
               '    /begin MOD_COMMON "" BYTE_ORDER MSB_LAST ALIGNMENT_BYTE 1 ALIGNMENT_WORD 1 ALIGNMENT_LONG 1 '
               'ALIGNMENT_INT64 1 ALIGNMENT_FLOAT32_IEEE 1 ALIGNMENT_FLOAT64_IEEE 1 /end MOD_COMMON\n']
        out += ['    /begin RECORD_LAYOUT %s %s /end RECORD_LAYOUT\n' % kv for kv in sorted(self.layouts.items())]
        for (eq, unit, dec), name in self.compus.items():
            out.append('    /begin COMPU_METHOD %s "" RAT_FUNC "%%8.%d" %s COEFFS %s /end COMPU_METHOD\n'
                       % (name, dec, _a2l_str(unit), ' '.join(_f(c) for c in rat_func(eq))))
        for name, e, cm, rl in self.axes.values():
            out.append('    /begin AXIS_PTS %s "" 0x%X NO_INPUT_QUANTITY %s 0 %s %d -1e38 1e38 /end AXIS_PTS\n'
                       % (name, BASE + e.address, rl, cm, e.n))
        out += self.chars
        out.append('  /end MODULE\n/end PROJECT\n')
        return ''.join(out)


def cmd_xdf2a2l(args):
    """
    Export an XDF as a reduced A2L: one CHARACTERISTIC per table, named by the A2L label its
    description starts with (else generated from the title), with record layouts, conversions
    and shared axis points built from the XDF. Fault-array tables become one VALUE per fault
    (<array>.DFC_<name>_C), the way the factory A2L stores them.

    Round trip: `a2l --a2l OUT.a2l --bin BIN --template SAME.xdf --fault-arrays` rebuilds the XDF.
    Axes are always written as shared AXIS_PTS, so the A2L is not byte-for-byte BMW's layout.
    """
    root = ET.parse(args.xdf).getroot()
    cats = {int(c.get('index'), 16) + 1: c.get('name') for c in root.iter('CATEGORY')}
    tables = list(root.iter('XDFTABLE'))
    axis_names = _xdf_axis_names(tables)

    w, groups, skipped = A2LWriter(), collections.defaultdict(list), []
    for tbl in tables:
        title = (tbl.findtext('title') or '').strip()
        if title.endswith('(autogen)'):
            continue
        desc = tbl.findtext('description') or ''
        m = LABEL_RE.match(desc)
        axes = {ax.get('id'): ax for ax in tbl.findall('XDFAXIS')}
        z = _xdf_axis(axes['z'])
        if z[0] != 'addr':
            skipped.append(title)
            continue
        ze, zeq, zunit, zdec = z[1], z[2], z[3], z[4]
        rows, cols = int(axes['z'].find('EMBEDDEDDATA').get('mmedrowcount', 1)), \
            int(axes['z'].find('EMBEDDEDDATA').get('mmedcolcount', 1))
        x, y = _xdf_axis(axes['x']), _xdf_axis(axes['y'])
        cat = _xdf_category(tbl, cats)

        if y[0] == 'labels' and cols == 1 and m and FAULT_ARRAY_RE.match(m.group(1)):  # a whole fault array
            dtype = w.dtype(ze)
            for i, label in enumerate(y[1]):
                n = '%s.DFC_%s_C' % (m.group(1), re.sub(r'\W', '_', label.split()[0]))
                if n not in w.names:
                    w.names.add(n)
                    w.chars.append('    /begin CHARACTERISTIC %s %s VALUE 0x%X %s 0 %s -1e38 1e38 /end CHARACTERISTIC\n'
                                   % (n, _a2l_str(label), BASE + ze.address + i * ze.step,
                                      w.layout('fnc', dtype), w.compu('X', '-', 0)))
            continue

        name = m.group(1) if m and A2L_NAME_RE.match(m.group(1)) else 'XDF_' + re.sub(r'\W+', '_', title).strip('_')
        if name in w.names:
            skipped.append('%s (duplicate name %s)' % (title, name))
            continue
        w.names.add(name)
        zmin, zmax = axes['z'].findtext('min'), axes['z'].findtext('max')
        colmajor = bool(ze.flags & 4) and rows > 1
        # axes stored right before the values (X, then Y) are inline STD_AXIS, as in BMW's A2L
        yi = y[0] == 'addr' and rows > 1 and y[1].address + y[1].size == ze.address
        xi = x[0] == 'addr' and x[1].address + x[1].size == (y[1].address if yi else ze.address)
        inline = {'x': xi, 'y': yi}
        if xi or yi:
            start = x[1].address if xi else y[1].address
            rl = w.std_layout(x[1] if xi else None, y[1] if yi else None, w.dtype(ze), colmajor)
        else:
            start, rl = ze.address, w.layout('fnc', w.dtype(ze), colmajor)
        head = '%s %s %%s 0x%X %s 0 %s %s %s' % (name, _a2l_str(title), BASE + start, rl,
                                                 w.compu(zeq, zunit, zdec), zmin or '-1e38', zmax or '1e38')

        def axis_descr(ax, count, letter):
            if ax[0] == 'addr' and inline[letter]:
                return ('      /begin AXIS_DESCR STD_AXIS %s %s %d -1e38 1e38 /end AXIS_DESCR\n'
                        % (axis_names.get(ax[1].address) or 'NO_INPUT_QUANTITY', w.compu(ax[2], ax[3], ax[4]), ax[1].n))
            if ax[0] == 'addr':
                ref = w.axis_pts(ax[1], ax[2], ax[3], ax[4], axis_names.get(ax[1].address) or 'AX_%X' % ax[1].address)
                return ('      /begin AXIS_DESCR COM_AXIS NO_INPUT_QUANTITY %s %d -1e38 1e38 AXIS_PTS_REF %s /end AXIS_DESCR\n'
                        % (w.axes[ax[1].address][2], ax[1].n, ref))
            vals = ax[1] if ax[0] == 'labels' else [str(i) for i in range(count)]
            unit, dec = (ax[2], ax[3]) if ax[0] == 'labels' else ('-', 0)
            return ('      /begin AXIS_DESCR FIX_AXIS NO_INPUT_QUANTITY %s %d -1e38 1e38 FIX_AXIS_PAR_LIST %s /end AXIS_DESCR\n'
                    % (w.compu('X', unit, dec), len(vals), ' '.join(vals)))

        if rows == 1 and cols == 1 and x[0] == 'plain':
            body = head % 'VALUE'
        elif x[0] == 'plain' and (rows == 1 or y[0] == 'plain'):
            body = (head % 'VAL_BLK') + ' MATRIX_DIM %d %d' % (cols, rows)
        elif rows == 1:
            body = (head % 'CURVE') + '\n' + axis_descr(x, cols, 'x') + '   '
        else:
            body = (head % 'MAP') + '\n' + axis_descr(x, cols, 'x') + axis_descr(y, rows, 'y') + '   '
        w.chars.append('    /begin CHARACTERISTIC %s /end CHARACTERISTIC\n' % body)
        if cat:
            groups[cat].append(name)

    for cat, names in groups.items():
        w.chars.append('    /begin GROUP %s %s /begin REF_CHARACTERISTIC %s /end REF_CHARACTERISTIC /end GROUP\n'
                       % (re.sub(r'\W+', '_', cat).strip('_') or 'Uncategorized', _a2l_str(cat), ' '.join(names)))
    header_desc = root.findtext('XDFHEADER/description') or ''
    project = args.project or re.sub(r'\W', '_', os.path.splitext(os.path.basename(args.xdf))[0])
    if project[0].isdigit():
        project = 'SW_' + project
    with open(args.output, 'w', encoding='latin-1', errors='replace') as f:  # A2Ls are Latin-1
        f.write(w.text(project, 'Reduced A2L exported by tools/xdftool.py xdf2a2l from %s. %s'
                       % (os.path.basename(args.xdf), header_desc)))
    print('wrote %s: %d characteristics, %d axis points, %d conversions, %d record layouts; %d tables skipped'
          % (args.output, len(w.chars) - len(groups), len(w.axes), len(w.compus), len(w.layouts), len(skipped)),
          file=sys.stderr)
    for t in skipped:
        print('  skipped: %s' % t, file=sys.stderr)


# ============================================================================
# WinOLS exports (kp, json): an XDF's tables as WinOLS maps
# ============================================================================

# WinOLS map organisation, as numbered in a map pack. Despite the name, "2D inverse" is TunerPro's
# usual row-major layout (X has cols points, Y rows, X varies fastest): every 2D map in a WinOLS pack
# for an ME7 read (nyetlabs/xdfkit testdata/archive/ecuxplot/8N0906018CB) is one and decodes that way.
# Plain "2D" is the other order, TunerPro's column-major flag.
OLS_SINGLE, OLS_1D, OLS_2D, OLS_2D_INV = 2, 3, 4, 5


def ols_scaling(eq):
    """A TunerPro equation as WinOLS scaling (factor, offset, reciprocal): physical = factor * raw +
    offset, or factor / raw + offset when reciprocal. None when it is neither."""
    a, b, c, d, e, f = rat_func(eq)  # raw = (b * physical + c) / (e * physical + f)
    if a or d:
        return None
    if b and not e:
        return f / b, -c / b, False
    if e and not b:
        return c / e, -f / e, True
    return None


def numeric(labels):
    """True when every axis label is a number (else they are text, e.g. fault names or 'Map 1')."""
    return all(re.match(r'-?\d*\.?\d+(?:[eE][+-]?\d+)?$', v.strip()) for v in labels)


def ols_maps(root):
    """The tables of a parsed XDF as WinOLS maps -> ([map], notes). '(autogen)' breakpoint tables are
    left out (WinOLS shows axes inside the map) and text-labelled rows (fault arrays) become a 1D list.
    A map's x / y is (_xdf_axis() result, A2L axis name), or None when its organisation has no such axis."""
    cats = {int(c.get('index'), 16) + 1: c.get('name') for c in root.iter('CATEGORY')}
    axis_names = _xdf_axis_names(root.iter('XDFTABLE'))

    def named(ax):
        return ax, axis_names.get(ax[1].address, '') if ax[0] == 'addr' else ''

    maps, notes = [], []
    for tbl in root.iter('XDFTABLE'):
        title = (tbl.findtext('title') or '').strip()
        if title.endswith('(autogen)'):
            continue
        axes = {ax.get('id'): ax for ax in tbl.findall('XDFAXIS')}
        z = _xdf_axis(axes['z'])
        if z[0] != 'addr':
            notes.append('%s: not addressed, left out' % title)
            continue
        ze, zeq, zunit, zdec = z[1:]
        emb = axes['z'].find('EMBEDDEDDATA')
        rows, cols = int(emb.get('mmedrowcount', 1)), int(emb.get('mmedcolcount', 1))
        x, y = _xdf_axis(axes['x']), _xdf_axis(axes['y'])
        if y[0] == 'labels' and cols == 1 and not numeric(y[1]):
            x, y, cols, rows = ('plain',), ('plain',), rows, 1
        scaling = ols_scaling(zeq)
        if not scaling:
            notes.append('%s (equation %s not linear: raw values)' % (title, zeq))
        org = (OLS_SINGLE if rows == cols == 1 else OLS_1D if rows == 1
               else OLS_2D if ze.flags & 4 else OLS_2D_INV)
        desc = tbl.findtext('description') or ''
        m = LABEL_RE.match(desc)
        maps.append({'title': title, 'desc': desc, 'id': m.group(1) if m else title[:64], 'cat': _xdf_category(tbl, cats),
                     'z': ze, 'scaling': scaling or (1.0, 0.0, False), 'unit': '' if zunit == '-' else zunit,
                     'dec': max(zdec, 0), 'rows': rows, 'cols': cols, 'org': org,
                     'x': named(x) if org > OLS_SINGLE else None, 'y': named(y) if org > OLS_1D else None})
    # the id is the A2L label a description starts with; hand-written descriptions give repeats
    ids = collections.Counter(m['id'] for m in maps)
    for m in maps:
        if ids[m['id']] > 1:
            m['id'] = m['title'][:64]
    return maps, notes


# ============================================================================
# kp: export an XDF as a WinOLS map pack
# ============================================================================

# Map pack (header 292, as written by WinOLS 5) layout, from nyetlabs/xdfkit docs/kp-format.md
# and kp/map.go: little-endian, strings are an int32 length + ISO-8859-15 bytes + NUL (none when
# empty). Map records sit in a one-entry zip "intern" (flag byte 0, int32 count, records).
KP_VALUE = [('description', 'str'), ('units', 'str'), ('factor', 'f64'), ('offset', 'f64')]
KP_AXIS = [('value', KP_VALUE), ('dataSource', 'i32'), ('addr', 'u32'), ('type', 'i32'), ('width', 'i32'), ('base', 'i32'),
        ('mirror', 'i32'), ('mirrorPad', 'raw9'), ('reciprocal', 'bool'), ('precision', 'i32'), ('signed', 'bool'),
        ('values', 'bytes'), ('dataHeader', 'i32'), ('signatureByte', 'i32')]
KP_MAP = [('marked', 'u8'), ('linkId', 'i32'), ('comment', 'str'), ('commentFlag', 'u8'), ('name', 'str'),
       ('organization', 'i32'), ('rightPane', 'i32'), ('type', 'i32'), ('width', 'i32'), ('base', 'i32'),
       ('folderId', 'i32'), ('id', 'str'), ('idPad', 'i32'), ('idFlag', 'u8'), ('idState', 'i32'),
       ('range', 'i64x6'), ('reciprocal', 'bool'), ('signed', 'bool'), ('difference', 'bool'), ('percent', 'bool'),
       ('cols', 'i32'), ('rows', 'i32'), ('cursor', 'i32x2'), ('precision', 'i32'), ('value', KP_VALUE),
       ('start', 'u32'), ('end', 'u32'), ('imageSize', 'i32'), ('imageSizePad', 'i32x2'), ('addr2', 'u32'),
       ('addr2Flags', 'i32x2'), ('addr2ImageSize', 'i32'), ('addr2Pad', 'i32'), ('x', KP_AXIS), ('y', KP_AXIS),
       ('yFlag', 'i32'), ('yPad', 'i16'), ('storedCols', 'i32'), ('storedRows', 'i32'), ('viewMode', 'i32'),
       ('viewFlags', 'u8x2'), ('view2DScale', 'f64x2'), ('view2DRef', 'i32'), ('viewFlag', 'u8'),
       ('view3DRotation', 'f64x2'), ('viewScale', 'f64'), ('viewScaleRef', 'i32'), ('viewOffset', 'f64'), ('term2', 'raw3')]
KP_FMT = {'u8': 'B', 'bool': '?', 'i16': 'h', 'i32': 'i', 'u32': 'I', 'f64': 'd', 'i64x6': '6q', 'i32x2': '2i', 'u8x2': '2B', 'f64x2': '2d'}

def kp_decode(b, pos, spec):
    out = {}
    for name, kind in spec:
        if isinstance(kind, list):
            out[name], pos = kp_decode(b, pos, kind)
        elif kind == 'str':
            n, = struct.unpack_from('<i', b, pos); pos += 4
            out[name] = b[pos:pos + n].decode('iso-8859-15'); pos += n + (1 if n > 0 else 0)
        elif kind == 'bytes':
            n, = struct.unpack_from('<i', b, pos); pos += 4
            out[name] = b[pos:pos + n]; pos += n
        elif kind.startswith('raw'):
            n = int(kind[3:]); out[name] = b[pos:pos + n]; pos += n
        else:
            f = '<' + KP_FMT[kind]; v = struct.unpack_from(f, b, pos); pos += struct.calcsize(f)
            out[name] = v[0] if len(v) == 1 else list(v)
    return out, pos

def kp_encode(d, spec):
    out = bytearray()
    for name, kind in spec:
        v = d[name]
        if isinstance(kind, list):
            out += kp_encode(v, kind)
        elif kind == 'str':
            s = v.encode('iso-8859-15', 'replace'); out += struct.pack('<i', len(s)) + (s + b'\0' if s else b'')
        elif kind == 'bytes':
            out += struct.pack('<i', len(v)) + v
        elif kind.startswith('raw'):
            assert len(v) == int(kind[3:]); out += v
        else:
            out += struct.pack('<' + KP_FMT[kind], *(v if isinstance(v, list) else [v]))
    return bytes(out)


KP_END_MARKER = bytes.fromhex('33887298')
KP_TYPE = {(1, False): 1, (2, False): 3, (4, False): 5, (4, True): 7}  # LSB-first: u8, 16-lohi, 32-lohi, float-lohi


def kp_zip(intern):
    """The one-entry zip WinOLS writes: raw deflate level 9, 'maximum' flag, DOS date 0."""
    z = zlib.compressobj(9, zlib.DEFLATED, -15)
    data = z.compress(intern) + z.flush()
    crc, name = zlib.crc32(intern), b'intern'
    common = struct.pack('<HHHHHIII', 20, 2, 8, 0, 0, crc, len(data), len(intern))
    local = b'PK\x03\x04' + common + struct.pack('<HH', len(name), 0) + name
    central = b'PK\x01\x02' + struct.pack('<H', 20) + common + struct.pack('<HHHHHII', len(name), 0, 0, 0, 0, 0x20, 0) + name
    eocd = b'PK\x05\x06' + struct.pack('<HHHHIIH', 0, 0, 1, 1, len(central), len(local) + len(data), 0)
    return local + data + central + eocd


def kp_frame(template):
    """Split a header-292 map pack into (head up to the zip length, offset of EndOffset in it,
    the MapsTag after the zip, its built-in folders, the trailing block)."""
    if struct.unpack_from('<i', template, 0x10)[0] not in (292, 329) or template[-4:] != KP_END_MARKER:
        sys.exit('--template must be a WinOLS 5 map pack (header 292)')
    z = template.find(b'PK\x03\x04')
    end_off = template.rfind(struct.pack('<i', len(template) - 4), 0, z)
    p = z + struct.unpack_from('<i', template, z - 4)[0]
    tag, (n,) = template[p:p + 12], struct.unpack_from('<i', template, p + 12)
    p += 16
    folders = []
    for _ in range(n):
        start = p
        ln = struct.unpack_from('<i', template, p + 8)[0]
        p += 12 + ln + (1 if ln else 0) + 2 + 4 + 15
        folders.append(template[start:p])
    return template[:z - 4], end_off, tag, folders, template[p:]


def kp_folder(fid, name):
    s = name.encode('iso-8859-15', 'replace')
    return struct.pack('<iii', fid, 0, len(s)) + (s + b'\0' if s else b'') + b'\x01\x01' + struct.pack('<i', 0x1000000) + bytes(15)


def kp_slot():
    """An axis record a map doesn't use."""
    return {'value': {'description': '', 'units': '', 'factor': 1.0, 'offset': 0.0}, 'dataSource': 0, 'addr': 0,
            'type': 1, 'width': 1, 'base': 16, 'mirror': 1, 'mirrorPad': bytes(9), 'reciprocal': False,
            'precision': 0, 'signed': False, 'values': b'', 'dataHeader': 0, 'signatureByte': -1}


def kp_axis(axis):
    """ols_maps() axis -> KP axis record."""
    if axis is None:
        return kp_slot()
    ax, name = axis
    rec = kp_slot()
    rec.update(base=10, mirror=0, precision=0)
    if ax[0] == 'addr':
        e, eq, unit, dec = ax[1:]
        factor, offset, recip = ols_scaling(eq) or (1.0, 0.0, False)
        rec.update(value={'description': name, 'units': '' if unit == '-' else unit, 'factor': factor, 'offset': offset},
                   dataSource=1, addr=e.address, type=KP_TYPE[(e.step, bool(e.flags & 0x10000))], width=e.step,
                   reciprocal=recip, precision=max(dec, 0), signed=bool(e.flags & 1))
    elif ax[0] == 'labels' and numeric(ax[1]):  # free editable: four bytes per point, in the axis type
        vals = [float(v) for v in ax[1]]
        whole = all(v.is_integer() for v in vals)
        rec.update(value={'description': name, 'units': '' if ax[2] == '-' else ax[2], 'factor': 1.0, 'offset': 0.0},
                   dataSource=4, type=5 if whole else 7, width=4, precision=max(ax[3], 0), signed=any(v < 0 for v in vals),
                   values=b''.join(struct.pack('<i', int(v)) if whole else struct.pack('<f', v) for v in vals))
    return rec


def cmd_kp(args):
    """
    Export an XDF as a WinOLS map pack (.kp, header 292 as WinOLS 5 writes it). One map per
    table: short id = the A2L label, name = the title, comment = the XDF description, a folder per
    category. Axes read from the bin, fixed axes as free-editable values, plain axes as ordinal.

    --template is any WinOLS 5 map pack (e.g. model/empty.kp from nyetlabs/xdfkit): its header,
    project block and trailing block are opaque to us and copied as they are.
    """
    root = ET.parse(args.xdf).getroot()
    region = root.find('XDFHEADER/REGION')
    image = int(region.get('size'), 16) if region is not None else 0

    head, end_off, maps_tag, builtin, trailing = kp_frame(read_bin(args.template))
    folder_ids, maps = {}, []
    tables, notes = ols_maps(root)
    for t in tables:
        ze, org, rows, cols, (factor, offset, recip) = t['z'], t['org'], t['rows'], t['cols'], t['scaling']
        if t['cat'] and t['cat'] not in folder_ids:
            folder_ids[t['cat']] = len(builtin) + len(folder_ids)
        rec = {'marked': 0, 'linkId': -1, 'comment': t['desc'], 'commentFlag': 0,
               'name': t['title'], 'organization': org, 'rightPane': 2, 'type': KP_TYPE[(ze.step, bool(ze.flags & 0x10000))],
               'width': ze.step, 'base': 10, 'folderId': folder_ids.get(t['cat'], 0), 'id': t['id'],
               'idPad': 0, 'idFlag': 0, 'idState': 1, 'range': [0, 255, 0, 0xFFFF, 0, 0xFFFFFFFF],
               'reciprocal': recip, 'signed': bool(ze.flags & 1), 'difference': False, 'percent': False,
               'cols': cols, 'rows': rows, 'cursor': [0, 0], 'precision': t['dec'],
               'value': {'description': '', 'units': t['unit'], 'factor': factor, 'offset': offset},
               'start': ze.address, 'end': ze.address + ze.size, 'imageSize': image, 'imageSizePad': [0, 0],
               'addr2': ze.address, 'addr2Flags': [-1, 0], 'addr2ImageSize': image, 'addr2Pad': 0,
               'x': kp_axis(t['x']), 'y': kp_axis(t['y']),
               'yFlag': 0, 'yPad': 0, 'storedCols': rows if org == OLS_2D_INV else cols,
               'storedRows': cols if org == OLS_2D_INV else rows,
               'viewMode': 1, 'viewFlags': [1, 1], 'view2DScale': [1.0, 1.0], 'view2DRef': -1, 'viewFlag': 1,
               'view3DRotation': [300.0, 1.0], 'viewScale': 0.0, 'viewScaleRef': -1, 'viewOffset': 0.0,
               'term2': b'\x01\x01\x01'}
        maps.append(rec)

    intern = b'\0' + struct.pack('<i', len(maps)) + b''.join(kp_encode(r, KP_MAP) for r in maps)
    zipped = kp_zip(intern)
    folders = builtin + [kp_folder(fid, name) for name, fid in folder_ids.items()]
    # the header's file name string (at 0x60): EndOffset moves by its change in length
    old_len = struct.unpack_from('<i', head, 0x60)[0]
    old_end = 0x64 + old_len + (1 if old_len else 0)
    name = os.path.basename(args.output).encode('iso-8859-15', 'replace')
    head = head[:0x60] + struct.pack('<i', len(name)) + name + b'\0' + head[old_end:]
    end_off += (0x64 + len(name) + 1) - old_end
    out = bytearray(head + struct.pack('<i', len(zipped)) + zipped + maps_tag + struct.pack('<i', len(folders))
                    + b''.join(folders) + trailing)
    struct.pack_into('<i', out, 0x14, len(out))       # HeaderLen: the file length
    struct.pack_into('<i', out, end_off, len(out) - 4)  # EndOffset: where the end marker starts
    with open(args.output, 'wb') as f:
        f.write(out)

    # read it back: every map decodes to the table it came from
    back = kp_read_maps(bytes(out))
    bad = [r['name'] for r, b in zip(maps, back) if (b['start'], b['end'], b['type'], b['cols'], b['rows']) !=
           (r['start'], r['end'], r['type'], r['cols'], r['rows'])]
    print('wrote %s: %d maps in %d folders, %d bytes; read back: %d maps, %d mismatches'
          % (args.output, len(maps), len(folders), len(out), len(back), len(bad) + abs(len(back) - len(maps))), file=sys.stderr)
    for t in notes:
        print('  note: %s' % t, file=sys.stderr)


def kp_read_maps(data):
    """Map records of a header-292 map pack."""
    z = data.find(b'PK\x03\x04')
    n = struct.unpack_from('<i', data, z - 4)[0]
    with zipfile.ZipFile(io.BytesIO(data[z:z + n])) as zf:
        intern = zf.read('intern')
    count, pos, maps = struct.unpack_from('<i', intern, 1)[0], 5, []
    for _ in range(count):
        rec, pos = kp_decode(intern, pos, KP_MAP)
        maps.append(rec)
    return maps


def kp_folders(data):
    """{folder id: name} of a header-292 map pack."""
    names = {}
    for rec in kp_frame(data)[3]:
        fid, _, n = struct.unpack_from('<iii', rec, 0)
        names[fid] = rec[12:12 + n].decode('iso-8859-15')
    return names


KP_DTYPE = {(1, False): 'UBYTE', (1, True): 'SBYTE', (3, False): 'UWORD', (3, True): 'SWORD',
            (5, False): 'ULONG', (5, True): 'SLONG', (7, False): 'FLOAT32_IEEE', (7, True): 'FLOAT32_IEEE'}


def cmd_kp2xdf(args):
    """
    Import a WinOLS map pack (header 292) as an XDF: a table per map, titled by the map name,
    described by its comment (else its id), in a category per folder, with breakpoint tables for the axes
    read from the bin. Map packs keep no min/max and no text row labels, so those are not restored.
    """
    data = read_bin(args.kp)
    b = Bin(args.bin)
    folders = kp_folders(data)
    cats = Categories()
    body, axes_done = [], set()
    for m in kp_read_maps(data):
        org, cols, rows = m['organization'], m['cols'], m['rows']

        def axis(ax, count):
            if ax['dataSource'] == 1:
                v = ax['value']
                return {'kind': 'addr', 'address': b.base + ax['addr'], 'dtype': KP_DTYPE[(ax['type'], bool(ax['signed']))],
                        'count': count, 'eq': _lin_eq(v['factor'], v['offset']), 'unit': v['units'],
                        'dec': ax['precision'], 'name': v['description']}
            if ax['dataSource'] == 4:
                n = len(ax['values']) // 4
                vals = struct.unpack('<%d%s' % (n, 'f' if ax['type'] == 7 else 'i'), ax['values'])
                return {'kind': 'labels', 'labels': list(vals), 'count': n, 'unit': ax['value']['units'], 'dec': ax['precision']}
            return None
        v = m['value']
        t = {'dtype': KP_DTYPE[(m['type'], bool(m['signed']))], 'eq': _lin_eq(v['factor'], v['offset']), 'unit': v['units'],
             'dec': m['precision'], 'lower': None, 'upper': None, 'rows': rows, 'cols': cols,
             'x': axis(m['x'], cols) if org > 2 else None, 'y': axis(m['y'], rows) if org > 3 else None,
             'colmajor': org == OLS_2D, 'address': b.base + m['start']}
        cat = [cats.id(folders[m['folderId']])] if m['folderId'] in folders and m['folderId'] > 1 else []
        desc = m['comment'] or m['id']
        body.append(table_xml(t, m['name'], desc, cat, b))
        for letter in ('x', 'y'):
            ax = t[letter]
            if ax and ax['kind'] == 'addr' and (ax['address'], ax['count']) not in axes_done:
                axes_done.add((ax['address'], ax['count']))
                body.append(axis_table_xml(ax, '%s %s (autogen)' % (m['name'], letter.upper()), cat, b))
    with open(args.output, 'w', encoding='utf-8', newline='\r\n') as f:
        f.write(xdf_document(args.description or 'Imported by tools/xdftool.py kp2xdf from %s' % os.path.basename(args.kp),
                             len(b.data), cats, body))
    print('wrote %s: %d tables (+%d axis tables)' % (args.output, len(body) - len(axes_done), len(axes_done)), file=sys.stderr)


# ============================================================================
# json: export an XDF as a WinOLS JSON map list
# ============================================================================

# The map list WinOLS exports as JSON (and its script import reads): one flat object per map, every
# value a string, ISO-8859-1, CRLF. Map types are German: Einzel(wert) / Eindim / Zweidim / ZweiInv.
OLS_JSON_TYPE = {OLS_SINGLE: 'eEinzel', OLS_1D: 'eEindim', OLS_2D: 'eZweidim', OLS_2D_INV: 'eZweiInv'}
OLS_JSON_ORG = {(1, True): 'eByte', (2, True): 'eLoHi', (2, False): 'eHiLo', (4, True): 'eLoHiLoHi', (4, False): 'eHiLoHiLo'}


def _ols_num(v):
    """A number the way WinOLS writes one: plain decimal, never an exponent."""
    v = float(v)
    return str(int(v)) if v.is_integer() else format(decimal.Decimal(repr(v)), 'f')


def _ols_org(e):
    if e.flags & 0x10000:
        return 'eFloatLoHi' if e.flags & 2 else 'eFloatHiLo'
    return OLS_JSON_ORG[(e.step, bool(e.flags & 2) or e.step == 1)]


def ols_json_axis(letter, axis):
    """ols_maps() axis -> the map's Axis<letter>.* fields."""
    rec = {'Name': '-', 'IdName': '', 'Unit': '-', 'Factor': '1', 'Offset': '0', 'Radix': '16', 'bBackwards': '1',
           'bReciprocal': '0', 'bSigned': '0', 'Precision': '-1', 'DataSrc': 'eDataSrcNone', 'DataHeader': '0',
           'DataAddr': '$0', 'DataOrg': 'eByte', 'SignatureByte': '0x-1', 'SkipBytes': '0'}  # an axis the map doesn't use
    ax, name = axis or (('plain',), '')
    if ax[0] == 'addr':
        e, eq, unit, dec = ax[1:]
        factor, offset, recip = ols_scaling(eq) or (1.0, 0.0, False)
        rec.update(Name=name or '%s axis' % letter, Unit=unit, Factor=_ols_num(factor), Offset=_ols_num(offset),
                   Radix='10', bBackwards='0', bReciprocal=str(int(recip)), bSigned=str(e.flags & 1),
                   Precision=str(max(dec, 0)), DataSrc='eRom', DataAddr='$%X' % e.address, DataOrg=_ols_org(e))
    elif ax[0] == 'labels':  # fixed breakpoints: WinOLS's own export leaves the values out, so add them as Values
        labels, unit, dec = ax[1:]
        rec.update(Name=name or '%s axis' % letter, Unit=unit, Radix='10', bBackwards='0', Precision=str(max(dec, 0)),
                   DataSrc='eUserdef' if numeric(labels) else 'eUserdefString', DataOrg='eFloatLoHi', Values=' '.join(labels))
    return [('Axis%s.%s' % (letter, k), v) for k, v in rec.items() if k != 'Values'] + \
        ([('Axis%s.Values' % letter, rec['Values'])] if 'Values' in rec else [])


def cmd_json(args):
    """
    Export an XDF as a WinOLS JSON map list: the format WinOLS writes with "Export > map list as
    JSON" and reads back with its script import, so it doesn't depend on a map pack header version.
    One map per table: IdName = the A2L label, Name = the title, Comment = the XDF description,
    FolderName = the category. Addresses are bin offsets, as in the XDF.

    Fixed axes (no address) get an Axis<X|Y>.Values list of their breakpoints, which WinOLS's own
    export doesn't carry. An output ending in .zip is a zip holding <name>.json.
    """
    tables, notes = ols_maps(ET.parse(args.xdf).getroot())
    maps = []
    for t in tables:
        ze, (factor, offset, recip) = t['z'], t['scaling']
        maps.append([('Name', t['title']), ('IdName', t['id']), ('FolderName', t['cat']), ('Type', OLS_JSON_TYPE[t['org']]),
                     ('ViewMode', 'eViewText'), ('RWin', 'eBars'), ('DataOrg', _ols_org(ze)),
                     ('bReciprocal', str(int(recip))), ('bSigned', str(ze.flags & 1)), ('bDelta', '0'), ('bPercent', '0'),
                     ('bOriginal', '0'), ('bOriginalValues', '0'), ('Columns', str(t['cols'])), ('Rows', str(t['rows'])),
                     ('Radix', '10'), ('Comment', t['desc']), ('Precision', str(t['dec'])), ('SkipBytes', '0'),
                     ('LineSkipBytes', '0'), ('Fieldvalues.Name', ''), ('Fieldvalues.Unit', t['unit']),
                     ('Fieldvalues.Factor', _ols_num(factor)), ('Fieldvalues.Offset', _ols_num(offset)),
                     ('Fieldvalues.StartAddr', '$%X' % ze.address)]
                    + ols_json_axis('X', t['x']) + ols_json_axis('Y', t['y']))
    text = '{\r\n  "maps" : [\r\n%s\r\n  ]\r\n}' % ',\r\n'.join(
        '    {\r\n%s\r\n    }' % ',\r\n'.join('      %s: %s' % (json.dumps(k), json.dumps(v, ensure_ascii=False)) for k, v in m)
        for m in maps)
    data = text.encode('latin-1', 'replace')
    out = data
    if args.output.lower().endswith('.zip'):
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as zf:
            zf.writestr(os.path.basename(args.output)[:-4], data)
        out = buf.getvalue()
    with open(args.output, 'wb') as f:
        f.write(out)

    # read it back: every map is there, at the table's address
    back = json.loads(data.decode('latin-1'))['maps']
    bad = sum(b['Fieldvalues.StartAddr'] != '$%X' % t['z'].address or b['Columns'] != str(t['cols'])
              for t, b in zip(tables, back)) + abs(len(back) - len(tables))
    ids = collections.Counter(t['id'] for t in tables)
    print('wrote %s: %d maps, %d bytes; read back: %d maps, %d mismatches; %d IdNames used more than once'
          % (args.output, len(maps), len(out), len(back), bad, sum(n > 1 for n in ids.values())), file=sys.stderr)
    for t in notes:
        print('  note: %s' % t, file=sys.stderr)


# ============================================================================
# Command line
# ============================================================================

def cmd_svk(args):
    """Print the software (SWFL) and calibration (SWFK) ids of each read, and the calibration's
    variant (car, market, emissions standard, power)."""
    for path in args.bins:
        data = read_bin(path)
        print(path)
        label = {'SWFL': 'software (SWFL)', 'SWFK': 'calibration (SWFK)'}
        for off, kind, svk in sorted(find_svk(data), key=lambda r: r[1] != 'SWFL'):
            print('  %-20s %s   at 0x%06X' % (label[kind], svk, off))
        print('  %-20s %s' % ('variant', variant(data) or '?'))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='command', required=True, metavar='COMMAND')

    def command(fn, summary):
        p = sub.add_parser(fn.__name__[4:], help=summary, description=fn.__doc__,
                           formatter_class=argparse.RawDescriptionHelpFormatter)
        p.set_defaults(run=fn)
        return p

    p = command(cmd_svk, 'software, calibration and variant ids of a read')
    p.add_argument('bins', nargs='+', metavar='BIN')

    p = command(cmd_a2l, 'build an XDF from the A2L')
    p.add_argument('--a2l', required=True)
    p.add_argument('--bin', required=True, help='flash read of the same software')
    p.add_argument('-o', '--output', required=True)
    p.add_argument('--template', action='append', default=[], help='XDF to take titles/categories from (repeatable)')
    p.add_argument('--names', action='append', default=[], help='LABEL[<TAB>Title[<TAB>Category]] file (repeatable)')
    p.add_argument('--fault-arrays', action='store_true', help='add a table per fault array, a row per fault')
    p.add_argument('--description', help='XDF header description')
    p.add_argument('--report', help='markdown report of skipped tables')
    p.add_argument('--base', default=hex(BASE), help='address at bin offset 0')
    p.add_argument('--no-axis-tables', action='store_true', help='skip the "(autogen)" breakpoint tables')
    p.add_argument('--no-cache', action='store_true', help='re-parse the A2L instead of using the cache')

    p = command(cmd_port, 'move an XDF to another software version')
    p.add_argument('--xdf', required=True)
    p.add_argument('--src-bin', required=True, help='read on the XDF\'s software')
    p.add_argument('--dst-bin', required=True, help='read on the new software, ideally the same car')
    p.add_argument('-o', '--output', required=True)
    p.add_argument('--a2l', help='A2L for the source software: more anchors, fault tables moved by fault index')
    p.add_argument('--extra', help='TSV of hand-placed tables to add')
    p.add_argument('--drop', help='regex: leave out tables whose title matches')
    p.add_argument('--drop-guessed', action='store_true')
    p.add_argument('--description', help='XDF header description for the new version')
    p.add_argument('--report')

    p = command(cmd_xdf2a2l, 'export an XDF as a reduced A2L')
    p.add_argument('--xdf', required=True)
    p.add_argument('-o', '--output', required=True)
    p.add_argument('--project', help='A2L project/module name (default: the XDF file name)')

    p = command(cmd_kp, 'export an XDF as a WinOLS map pack (.kp)')
    p.add_argument('--xdf', required=True)
    p.add_argument('--template', required=True, help='any WinOLS 5 map pack (header 292) to take the file frame from')
    p.add_argument('-o', '--output', required=True)

    p = command(cmd_kp2xdf, 'import a WinOLS map pack (.kp) as an XDF')
    p.add_argument('--kp', required=True)
    p.add_argument('--bin', required=True, help='a read of the same software (for the file size)')
    p.add_argument('-o', '--output', required=True)
    p.add_argument('--description', help='XDF header description')

    p = command(cmd_json, 'export an XDF as a WinOLS JSON map list')
    p.add_argument('--xdf', required=True)
    p.add_argument('-o', '--output', required=True, help='.json, or .json.zip for a zip holding the .json')

    p = command(cmd_diff, 'what a tune changed, table by table')
    p.add_argument('--xdf', required=True, help='XDF for the stock read')
    p.add_argument('--stock', required=True)
    p.add_argument('--tune', required=True)
    p.add_argument('--tune-xdf', help='XDF for the tune, when it is on another software version')
    p.add_argument('--report')
    p.add_argument('--all-values', action='store_true', help='full value lists, not just ranges')
    p.add_argument('--region', default='0x%X:0x%X' % CAL, help='START:END to compare, or "all" (default: cal area)')

    p = command(cmd_transfer, "copy a tune onto another car's stock read")
    p.add_argument('--xdf', required=True, help='XDF for the source software')
    p.add_argument('--src-stock', required=True)
    p.add_argument('--src-tune', required=True)
    p.add_argument('--dst-stock', required=True, help="customer's stock read")
    p.add_argument('--dst-xdf', help="XDF for the customer's software (required when it differs)")
    p.add_argument('-o', '--output', required=True)
    p.add_argument('--report')
    p.add_argument('--exclude', help='regex on table title/category to leave out')
    p.add_argument('--no-moved', action='store_true', help='only write "exact" tables')

    args = ap.parse_args()
    args.run(args)


if __name__ == '__main__':
    main()
