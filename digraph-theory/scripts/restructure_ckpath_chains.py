#!/usr/bin/env python3
"""Restructure the committed ck_path micro-block chains (arthur, phase-2 DRAFT for Lancelot 20e0b09e; NOT RUN).
Design: ckpath-restructure-design-by-arthur (7e8d05aa), section b.  Untrusted build-time tool, like the generator: Rocq re-checks
everything it emits.  Deterministic; reads TREE, writes only OUT.

  restructure_ckpath_chains.py TREE OUT [--round-trip-only] [--groups G1,G2,...]

TREE is a clean checkout root (digraph-theory/... under it).  For every chain group (files <g>_blockNN.v + <g>_final.v in ck_path):
  1. PARSE each block with anchored patterns (fields carried as raw text) and REFUSE on any mismatch;
  2. ROUND-TRIP: render_old_block(fields) must equal the committed bytes, for every block and every final (this is what proves the
     parse captured the whole file: nothing outside the fields can differ);
  3. VALIDATE: labels 0..n-1 of one width; producers precede (index < K); each selection names its producer's _output / _sound;
     the generated comment's counts equal the data (producers, imported indices, selected-base clauses or base ids, records = b - a);
     one base expression per group, equal to the final's; the final names the last block;
  4. EMIT (unless --round-trip-only): OUT/ck_path/<g>_<label>_data.v, <g>_<label>.v (replay), <g>_assembly.v, <g>_final.v;
     OUT/_CoqProject = TREE's digraph-theory/_CoqProject with the new .v entries APPENDED (data files, then assemblies; additions only);
  5. DATA-LITERAL CHECK on the emitted text: each block's output literal is in its data file and not in its replay; its records and
     selected_base / base_ids literals are in its replay; every index list is in the replay and in the assembly;
  6. OUT/manifest.sha256 (every emitted file) and OUT/summary.json; a second run must reproduce the manifest byte for byte."""
from __future__ import annotations

import argparse, hashlib, json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ckpath_chain_render as R  # noqa: E402

CK = 'digraph-theory/theories/applications/ck_path'
COQPROJECT = 'digraph-theory/_CoqProject'
STEM = re.compile(r'(?P<g>.+)_(?P<label>block(?P<k>\d+))')
REQ = re.compile(r'^From Digraph Require Import (?P<mods>[^\n]+)\.$', re.M)
COMMENT = re.compile(r'^\(\*\* Original retained additions \[(\d+), (\d+)\); (\d+) selected base clauses and (\d+) imported '
                     r'consequences from (\d+) producer blocks\.(?P<close> \*\))?$', re.M)
IDS_LINE = re.compile(r'^    Original selected base identifiers: (?P<ids>\[[0-9;]*\])\. \*\)$', re.M)
OUTPUT = re.compile(r'^Definition (?P<name>\w+)_(?P<label>block\d+)_output : cnf :=\n  ', re.M)
BASE = re.compile(r'^  forall rho, satisfies_cnf rho \((?P<base>.*)\) ->$', re.M)
SEL = re.compile(r'^pose \(select_cnf (?P<po>\w+) (?P<idx>\[[0-9;]*\]) : cnf\)\n  as imported_from_(?P<pl>block\d+)\.$', re.M)
BASE_IDS = re.compile(r'^pose \(\n  (?P<ids>\[[0-9;]*\]) : list nat\) as base_ids\.$', re.M)
REC_OPEN, REC_CLOSE = 'pose ([\n', '] : list (list nat * list nat)) as records.\n'
FINAL_REQ = re.compile(r'^From Digraph Require Import ckpath_cnf (?P<bm>\S+) (?P<g>\S+)_(?P<label>block\d+)\.$', re.M)
FINAL_THM = re.compile(r'^Theorem (?P<name>\w+)_base_unsatisfiable :\n  forall rho, ~ satisfies_cnf rho \((?P<base>.*)\)\.$', re.M)
FMT_OF = {'ckpath_drup_explicit_microblock': 'explicit', 'ckpath_drup_microblock': 'selected'}


class Refused(Exception):
    pass


def need(ok, *what):
    if not ok:
        raise Refused(' '.join(str(w) for w in what))


def one(rx, text, what):
    ms = list(rx.finditer(text))
    need(len(ms) == 1, 'expected exactly one', what, 'found', len(ms))
    return ms[0]


def between(text, start, end, what):
    i = text.find(start)
    need(i >= 0 and text.find(start, i + 1) < 0, 'expected exactly one opening of', what)
    j = text.find(end, i + len(start))
    need(j >= 0, 'no closing of', what)
    return text[i + len(start):j]


def cnf_clauses(raw):
    if raw == '[]':
        return 0
    lines = raw.split('\n')
    need(lines[0] == '[' and lines[-1] == ']' and all(l.startswith('  [') for l in lines[1:-1]), 'a cnf literal is not in write_rocq_cnf form')
    return len(lines) - 2


def nats(raw):
    return [] if raw == '[]' else raw[1:-1].split(';')


def parse_block(path: Path) -> R.Block:
    text = path.read_text(encoding='ascii')
    m = STEM.fullmatch(path.stem)
    need(m, 'not a block file name', path.name)
    g, label = m.group('g'), m.group('label')
    mods = one(REQ, text, 'Digraph Require line').group('mods').split(' ')
    need(len(mods) >= 3 and mods[0] == 'ckpath_cnf' and mods[1] in FMT_OF, 'unexpected Require line', mods[:3])
    fmt, base_module = FMT_OF[mods[1]], mods[2]
    prod_labels = []
    for mod in mods[3:]:
        pm = STEM.fullmatch(mod)
        need(pm and pm.group('g') == g, 'a non-producer module in the Require line', mod)
        prod_labels.append(pm.group('label'))
    c = one(COMMENT, text, 'counts comment')
    need((c.group('close') is None) == (fmt == 'explicit'), 'the comment form does not match the format', fmt)
    o = one(OUTPUT, text, 'output definition')
    need(o.group('label') == label, 'output label differs from the file name', o.group('label'), label)
    name = o.group('name')
    output = between(text, o.group(0), '.\n\nTheorem ', 'output literal')
    bases = {x.group('base') for x in BASE.finditer(text)}
    need(len(bases) == 1, 'not exactly one base expression', bases)
    sels = [R.Selection(x.group('pl'), x.group('idx')) for x in SEL.finditer(text)]
    for x, s in zip(SEL.finditer(text), sels):
        need(x.group('po') == '%s_%s_output' % (name, s.label), 'a selection names a foreign output', x.group('po'))
    need([s.label for s in sels] == prod_labels, 'the selections differ from the Require line producers', prod_labels)
    b = R.Block(fmt=fmt, group=g, label=label, name=name, base_module=base_module, base=bases.pop(),
                counts=c.groups()[:5],
                base_ids_comment=one(IDS_LINE, text, 'base ids comment').group('ids') if fmt == 'explicit' else None,
                selected_base=between(text, 'Definition selected_base : cnf :=\n  ', '.\n\nDefinition ', 'selected_base') if fmt == 'explicit' else None,
                base_ids=one(BASE_IDS, text, 'base_ids pose').group('ids') if fmt == 'selected' else None,
                output=output, records=between(text, REC_OPEN, REC_CLOSE, 'records'), selections=sels)
    old = R.render_old_block(b)
    if old != text:
        i = next((k for k, (p, q) in enumerate(zip(old, text)) if p != q), min(len(old), len(text)))
        raise Refused('ROUND-TRIP differs at byte %d: committed %r rendered %r' % (i, text[max(0, i - 40):i + 40], old[max(0, i - 40):i + 40]))
    a, z, nb, ni, np = (int(v) for v in b.counts)
    need(np == len(sels), 'producer count', np, len(sels))
    need(ni == sum(len(nats(s.indices)) for s in sels), 'imported count', ni)
    if fmt == 'explicit':
        need(nb == cnf_clauses(b.selected_base) == len(nats(b.base_ids_comment)), 'selected base count', nb)
    else:
        need(nb == len(nats(b.base_ids)), 'base ids count', nb)
    need(z - a == b.records.count('\n'), 'records count', z - a, b.records.count('\n'))
    k = int(label[len('block'):])
    need(all(int(s.label[len('block'):]) < k for s in sels), 'a producer does not precede its consumer', label)
    return b


def parse_final(path: Path, blocks: list) -> R.Final:
    text = path.read_text(encoding='ascii')
    q = one(FINAL_REQ, text, 'final Require line')
    t = one(FINAL_THM, text, 'final theorem')
    last = blocks[-1]
    f = R.Final(group=q.group('g'), name=t.group('name'), base_module=q.group('bm'), last_label=q.group('label'), base=t.group('base'),
                rights=len(re.findall(r'(?m)^  right\.$', text)))     # r2: str.count('\n  right.\n') counted non-overlapping (half)
    need(f.group == last.group and f.last_label == last.label and f.name == last.name and f.base == last.base
         and f.base_module == last.base_module, 'the final does not close its group', path.name)
    need(f.rights == cnf_clauses(last.output) - 1, 'the final\'s right count is not the last output length - 1')
    need(R.render_old_final(f) == text, 'ROUND-TRIP of the final differs', path.name)
    return f


def groups_of(tree: Path, only=None):
    ck = tree / CK
    by = {}
    for p in sorted(ck.glob('*_block*.v')):
        m = STEM.fullmatch(p.stem)
        if m:
            by.setdefault(m.group('g'), []).append(p)
    out = {}
    for g, ps in sorted(by.items()):
        if only and g not in only:
            continue
        need((ck / (g + '_final.v')).is_file(), 'a group without its final', g)
        ks = sorted(int(STEM.fullmatch(p.stem).group('k')) for p in ps)
        widths = {len(STEM.fullmatch(p.stem).group('k')) for p in ps}
        need(ks == list(range(len(ps))) and len(widths) == 1, 'labels are not 0..n-1 of one width', g)
        out[g] = sorted(ps, key=lambda p: int(STEM.fullmatch(p.stem).group('k')))
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('tree', type=Path)
    ap.add_argument('out', type=Path)
    ap.add_argument('--round-trip-only', action='store_true')
    ap.add_argument('--groups', default='')
    a = ap.parse_args(argv)
    if a.out.exists():
        raise SystemExit('REFUSED: %s exists' % a.out)
    only = set(filter(None, a.groups.split(',')))
    summary = {'tree': str(a.tree), 'groups': {}, 'emitted': 0}
    emitted = {}
    try:
        G = groups_of(a.tree, only)
        need(G, 'no group selected')
        for g, ps in G.items():
            blocks = [parse_block(p) for p in ps]
            need(len({(b.fmt, b.base, b.base_module, b.name) for b in blocks}) == 1, 'a group mixes formats, bases or names', g)
            fin = parse_final(a.tree / CK / (g + '_final.v'), blocks)
            summary['groups'][g] = {'format': blocks[0].fmt, 'blocks': len(blocks), 'round_trip': 'byte-exact', 'name': blocks[0].name}
            if a.round_trip_only:
                continue
            for b in blocks:
                emitted['%s/%s_data.v' % (CK, b.module())] = R.render_data(b)
                emitted['%s/%s.v' % (CK, b.module())] = R.render_replay(b)
            emitted['%s/%s_assembly.v' % (CK, g)] = R.render_assembly(blocks)
            emitted['%s/%s_final.v' % (CK, g)] = R.render_new_final(fin)
            for b in blocks:                                    # 5. the data-literal check
                d, r = emitted['%s/%s_data.v' % (CK, b.module())], emitted['%s/%s.v' % (CK, b.module())]
                asm = emitted['%s/%s_assembly.v' % (CK, g)]
                need(b.output in d and b.output not in r, 'output literal not moved verbatim', b.module())
                need(b.records in r, 'records not carried verbatim', b.module())
                need((b.selected_base or b.base_ids) in r, 'selected base / base ids not carried verbatim', b.module())
                need(all(s.indices in r and s.indices in asm for s in b.selections), 'an index list not carried', b.module())
    except Refused as e:
        raise SystemExit('REFUSED: %s' % e)
    if a.round_trip_only:
        a.out.mkdir(parents=True)
        (a.out / 'summary.json').write_text(json.dumps(summary, indent=1, sort_keys=True) + '\n')
        print('ROUND_TRIP_OK %d groups, %d blocks' % (len(summary['groups']), sum(v['blocks'] for v in summary['groups'].values())))
        return 0
    cq = (a.tree / COQPROJECT).read_text(encoding='ascii')
    need_new = [p[len('digraph-theory/'):] for p in sorted(emitted) if p.endswith(('_data.v', '_assembly.v'))]
    lines = set(cq.splitlines())
    if any(n in lines for n in need_new) or not cq.endswith('\n'):
        raise SystemExit('REFUSED: _CoqProject already lists a new file, or lacks its final newline')
    new_cq = cq + ''.join(n + '\n' for n in [x for x in need_new if x.endswith('_data.v')] + [x for x in need_new if x.endswith('_assembly.v')])
    a.out.mkdir(parents=True)
    for rel, txt in sorted(emitted.items()):
        p = a.out / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(txt, encoding='ascii')
    (a.out / COQPROJECT).parent.mkdir(parents=True, exist_ok=True)
    (a.out / COQPROJECT).write_text(new_cq, encoding='ascii')
    files = sorted(list(emitted) + [COQPROJECT])
    (a.out / 'manifest.sha256').write_text(''.join('%s  %s\n' % (hashlib.sha256((a.out / f).read_bytes()).hexdigest(), f) for f in files))
    summary['emitted'] = len(files)
    summary['coqproject_added'] = len(need_new)
    (a.out / 'summary.json').write_text(json.dumps(summary, indent=1, sort_keys=True) + '\n')
    print('RESTRUCTURE_OK %d groups, %d blocks, %d files emitted, %d _CoqProject entries appended'
          % (len(summary['groups']), sum(v['blocks'] for v in summary['groups'].values()), len(files), len(need_new)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
