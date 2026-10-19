#!/usr/bin/env python3
"""Validate/render the reviewed manuscript ledger; never infer mathematical coverage.

Author edits belong in docs/equation-map.json. A new source/PDF snapshot requires
manual mapping review and an explicitly updated snapshot there. --write only
renders reviewed data; it does not change the accepted hashes or audit evidence.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
STATUSES = {'definition', 'assumption', 'proved_identity', 'conditional_implication',
            'open_derivation', 'specification_target', 'conjecture', 'known_mismatch'}
LOGICAL = {'propext', 'Classical.choice', 'Quot.sound'}
PERMITTED = {'AsymmetricTensor.' + x for x in ('c', 'l_p', 'hbar', 'c_pos', 'l_p_pos', 'hbar_pos')}
# Evidence files are never loaded by Lake or installed over the current checkout.
ARCHIVED_FILES = {
    'AsymmetricTensor.lean': 'docs/equation-baseline-source.lean.txt',
    'lake-manifest.json': 'docs/equation-baseline-lake-manifest.json.txt',
    'tests/EquationAxioms.lean': 'docs/equation-baseline-axiom-audit.lean.txt',
}

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def canonical(value):
    return json.dumps(value, ensure_ascii=False, indent=2) + '\n'

def source_declarations(source):
    found = {}
    for i, line in enumerate(source.splitlines(), 1):
        m = re.match(r'^(?:noncomputable )?(def|abbrev|axiom|opaque|theorem|lemma)\s+(\w+)', line)
        if m:
            found['AsymmetricTensor.' + m[2]] = {'source_line': i, 'source_kind': m[1]}
    return found

def equation_inventory(pdf):
    text = subprocess.run(['pdftotext', '-layout', str(pdf), '-'], check=True,
                          capture_output=True, text=True).stdout
    found = {}
    sections = {}
    main = 0
    current = '1'
    for page, content in enumerate(text.split('\f'), 1):
        lines = content.splitlines()
        for index, line in enumerate(lines):
            # Only sequential, flush-left main headings; numbered prose is indented.
            m = re.match(r'^(\d{1,2})\.\s+(.+)$', line)
            if m and int(m[1]) == main + 1 and int(m[1]) <= 16:
                main = int(m[1]); current = str(main)
                sections[current] = {'id': current, 'page': page, 'title': m[2]}
            sub = re.match(r'^(\d{1,2}\.\d+)\s+(.+)$', line)
            if sub and int(sub[1].split('.')[0]) == main:
                current = sub[1]
                sections[current] = {'id': current, 'page': page, 'title': sub[2]}
            m = re.search(r'\((\d+)\)\s*$', line)
            if not m or not 1 <= int(m[1]) <= 239:
                continue
            # One prose reference to (105) ends a line; it is not a displayed label.
            if re.search(r'\b[Ee]quation\s+\(\d+\)\s*$', line):
                continue
            number = int(m[1])
            if number in found:
                raise ValueError(f'Duplicate displayed equation {number}')
            found[number] = {'page': page, 'section': current,
                             'pdf_label': f'({number})'}
    if set(found) != set(range(1, 240)):
        raise ValueError('PDF numbered equation inventory changed')
    if set(str(i) for i in range(1, 17)) - sections.keys():
        raise ValueError('PDF main section inventory changed')
    return found, list(sections.values())

def verify_snapshot(root, snapshot, historical=False):
    for path, expected in snapshot['files'].items():
        evidence_path = ARCHIVED_FILES.get(path, path) if historical else path
        actual = digest(root / evidence_path)
        if actual != expected:
            raise ValueError(f'Stale reviewed snapshot: {path}: {actual} != {expected}; review mappings before updating the accepted hash')

def verify_archives(root, snapshot):
    for path, archive in ARCHIVED_FILES.items():
        if digest(root / archive) != snapshot['files'][path]:
            raise ValueError(f'Archived snapshot evidence changed: {path}')

def audit_from_log(log, source, snapshot):
    records = []
    count = None
    for line in log.splitlines():
        if line.startswith('EQUATION_AXIOM '):
            records.append(json.loads(line[len('EQUATION_AXIOM '):]))
        elif line.startswith('EQUATION_AXIOM_COUNT '):
            count = int(line.split()[-1])
    if not count or count != len(records):
        raise ValueError('Incomplete Lean axiom output')
    declared = source_declarations(source)
    for item in records:
        if item['name'] in declared:
            item.update(declared[item['name']])
            item['generated'] = False
        else:
            candidates = [n for n in declared if item['name'].startswith(n + '.')]
            item['generated'] = True
            if candidates:
                owner = max(candidates, key=len)
                item['source_parent'] = owner
                item['source_line'] = declared[owner]['source_line']
    data = {'schema_version': 1, 'snapshot_files': snapshot['files'],
            'method': 'Lean collectAxioms for every declaration owned by the AsymmetricTensor module (including generated declarations), plus Meta.ppExpr for complete elaborated types.',
            'standard_logical_axioms': sorted(LOGICAL), 'allowed_custom_axioms': sorted(PERMITTED),
            'declaration_count': len(records), 'source_declaration_count': len(declared),
            'declarations': records}
    validate_audit(data, source, snapshot)
    return data

def validate_audit(audit, source, snapshot):
    if audit['snapshot_files'] != snapshot['files']:
        raise ValueError('Audit and mapping snapshots differ')
    if audit['source_declaration_count'] != len(source_declarations(source)):
        raise ValueError('Source declaration count changed')
    decls = audit['declarations']; names = [d['name'] for d in decls]
    if len(names) != len(set(names)) or len(names) != audit['declaration_count']:
        raise ValueError('Duplicate/inconsistent audit inventory')
    expected = source_declarations(source)
    if set(expected) - set(names):
        raise ValueError('Missing source declaration from audit')
    actual_source = {d['name'] for d in decls if not d.get('generated')}
    if actual_source != set(expected):
        raise ValueError('Source declaration flags differ from inspected source')
    axioms = {d['name'] for d in decls if d['kind'] == 'axiom'}
    if axioms != PERMITTED:
        raise ValueError('Explicit custom axiom inventory changed')
    for d in decls:
        if d['name'] in expected:
            if any(d.get(k) != v for k, v in expected[d['name']].items()):
                raise ValueError(f'Stale source location/kind: {d["name"]}')
        if d.get('generated') and not d.get('source_parent'):
            raise ValueError('Generated declaration has no reviewed source owner')
        if d.get('generated'):
            parent = d['source_parent']
            if (parent not in expected or not d['name'].startswith(parent + '.')
                    or d.get('source_line') != expected[parent]['source_line']):
                raise ValueError(f'Stale generated declaration owner: {d["name"]}')
        ax = set(d['axioms'])
        if ax - LOGICAL - PERMITTED or set(d['custom_axioms']) != ax - LOGICAL:
            raise ValueError(f'Unreviewed transitive axioms: {d["name"]}')
        if not d['type'] or '⋯' in d['type']:
            raise ValueError('Missing or abbreviated elaborated type')
    return {d['name']: d for d in decls}

def validate_mapping(mapping, inventory, audit, source):
    lookup = validate_audit(audit, source, mapping['snapshot'])
    rows = mapping['entries']; ids = [r['id'] for r in rows]
    if len(ids) != len(set(ids)):
        raise ValueError('Duplicate equation/claim identifiers')
    numbered = {r['id'] for r in rows if isinstance(r['id'], int)}
    if numbered != set(inventory):
        raise ValueError('Numbered coverage must be exactly 1–239')
    unnumbered = [r for r in rows if isinstance(r['id'], str)]
    roadmap = [r for r in unnumbered if r['section'].split('.')[0] == '16']
    if len(unnumbered) != 40 or len(roadmap) != 29:
        raise ValueError('Reviewed unnumbered inventory must contain 29 roadmap and 11 foundational claims')
    for row in rows:
        if row['status'] not in STATUSES or not row['topic'].strip() or not row['note'].strip():
            raise ValueError(f'Incomplete status/scope in {row["id"]}')
        if any(n not in lookup for n in row['declarations']):
            raise ValueError(f'Unknown declaration in {row["id"]}')
        if row['status'] == 'proved_identity' and not row['declarations']:
            raise ValueError('Proved identity requires declaration evidence')
        if isinstance(row['id'], str) and not (1 <= row['page'] <= 56 and row['section']):
            raise ValueError('Unnumbered claim needs PDF page and section')
    targets = []
    starts = list(re.finditer(r'^(?:theorem|lemma)\s+(\w+)', source, re.M))
    for i, match in enumerate(starts):
        end = starts[i+1].start() if i+1 < len(starts) else len(source)
        if re.search(r'\bexact h_target\b', source[match.start():end]):
            targets.append('AsymmetricTensor.' + match[1])
    if len(targets) != 10:
        raise ValueError('Exact-target inventory changed; review specification labels')
    for name in targets:
        mapped = [r for r in rows if name in r['declarations'] and r['status'] == 'specification_target']
        if not mapped:
            raise ValueError(f'Unlabelled exact-target specification: {name}')
    return lookup

def esc(text):
    return str(text).replace('|', '\\|').replace('\n', ' ')

def render(mapping, inventory, sections, audit, source):
    lookup = validate_mapping(mapping, inventory, audit, source)
    rows = []
    for original in mapping['entries']:
        row = dict(original)
        if isinstance(row['id'], int):
            evidence = inventory[row['id']]
            if 'page' in row and row['page'] != evidence['page']:
                raise ValueError(f'Wrong PDF page for equation {row["id"]}')
            if 'section' in row and row['section'].split('.')[0] != evidence['section'].split('.')[0]:
                raise ValueError(f'Wrong main section for equation {row["id"]}')
            row['page'] = evidence['page']
            row.setdefault('section', evidence['section'])
            row['pdf_label'] = evidence['pdf_label']
        row['pdf_url'] = mapping['snapshot']['pdf_url'] + '#page=' + str(row['page'])
        row['declaration_evidence'] = [
            {'name': n, 'source_line': lookup[n]['source_line'],
             'audit_ref': 'declaration-audit.json#' + n,
             'custom_axioms': lookup[n]['custom_axioms']} for n in row['declarations']]
        rows.append(row)
    section_ids = {s['id'] for s in sections}
    for sec in mapping.get('additional_sections', []):
        if sec['id'] not in section_ids:
            sections.append(sec)
            section_ids.add(sec['id'])
    sections.sort(key=lambda s: [int(x) for x in s['id'].split('.')])
    if any(r['section'] not in section_ids for r in rows):
        raise ValueError('Mapped subsection absent from navigation inventory')
    result = {'schema_version': 1, 'snapshot': mapping['snapshot'],
              'meaning': mapping['meaning'], 'sections': sections,
              'counts': dict(Counter(r['status'] for r in rows)),
              'numbered_equations': len(inventory), 'unnumbered_claims': len(rows)-len(inventory),
              'declaration_audit': {'path': 'declaration-audit.json',
                                    'declarations': audit['declaration_count'],
                                    'source_declarations': audit['source_declaration_count']},
              'entries': rows}
    md = ['# Historical equation-level coverage and assumption ledger', '',
          'This is the **historical v9 / #9+#33 snapshot ledger**. It does not describe current-source coverage or claim full physical formalization. '
          'It addresses the equation-level accounting requested by [#29](https://github.com/lilalittle/asymmetric-tensor/issues/29).', '',
          '## Exact snapshot and limits', '',
          '- Manuscript: September 25, 2026, v9, [Zenodo 22953897](https://doi.org/10.5281/zenodo.22953897).',
          '- Source: reviewed baseline `9f69988d17c9fb86f35a563eb6466be9dbf4e524` plus the included #9 conservation repair and #33 scope documentation.',
          '- Later #10, #11, #25, #26 and #27 repairs are **not included in this ledger**. The current repository has changed since the reviewed snapshot; historical mismatch labels below must not be read as findings about the repaired current source. See the [current scope map](formalization-status.md) for subsequent changes.',
          '- The exact reviewed source is preserved as [immutable text evidence](equation-baseline-source.lean.txt). It is not production code or a build target. All source links below point to this archive, so later repairs cannot silently change the referenced statement.',
          '- The snapshot dependency manifest is preserved as [immutable text evidence](equation-baseline-lake-manifest.json.txt). It is not the current dependency selection and must not replace the production `lake-manifest.json`.',
          '- No current-source equation audit, manuscript correction, fresh-checkout run or remote CI result is implied by this historical evidence.', '']
    for path, sha in mapping['snapshot']['files'].items():
        md.append(f'- `{path}` SHA-256: `{sha}`')
    md += ['', f'All **{len(inventory)} numbered equations (1–239)** and **{len(rows)-len(inventory)} substantive unnumbered claims** have explicit entries. '
           f'The companion [kernel audit](declaration-audit.json) includes **{audit["declaration_count"]} declarations**, '
           f'comprising **{audit["source_declaration_count"]} source declarations** and generated declarations.', '',
           'The 29 unnumbered manuscript roadmap entries in section 16 correspond to 27 Lean theorems: two manuscript entries have no declaration. The other 11 unnumbered entries cover foundational claims outside section 16.', '',
           'The machine-readable [reviewed map](equation-map.json) supplies judgments; '
           '[coverage JSON](equation-coverage.json) joins them to verified PDF pages and declaration evidence. '
           'The audit supplies each declaration’s complete elaborated type, including every hypothesis and implicit parameter, '
           'and its full transitive axiom list. Declaration names in the tables link to source lines. '
           'A “related only” entry is navigation evidence, **not** a completed mapping.', '',
           '## Status key', '',
           '- **proved_identity**: kernel-checked algebra for the exact implemented objects, with physical limitations stated.',
           '- **conditional_implication**: conclusion follows from supplied model equations or other substantive hypotheses.',
           '- **definition**: a model expression is introduced, not derived.',
           '- **assumption**: the manuscript relationship enters as a premise or modeling identification.',
           '- **open_derivation**: required objects or proof are absent; related scalar stand-ins may exist.',
           '- **specification_target**: the conclusion is supplied as `h_target` and returned unchanged.',
           '- **conjecture**: roadmap claim without an implemented construction or proof.',
           '- **known_mismatch**: the paper interpretation/formula does not match this source snapshot.', '',
           'Labels apply to the scope described in each note. A proved identity does not validate the surrounding physical interpretation. '
           'An open derivation does not claim the paper is false. A correct implication with an assumed target is not an invalid Lean proof.', '',
           '## Assumptions and missing constructions', '',
           'The only custom axioms reported transitively are `c`, `l_p`, `hbar`, and their three positivity axioms. '
           'Standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`) are listed separately. '
           'No audited declaration depends on `sorryAx` or the removed universal conservation axiom. '
           'This is a complete declaration audit for the identified module snapshot, not a consistency proof or a claim that physical assumptions are limited to six axioms. '
           'The nine body-less opaque fields, theorem hypotheses, parameterized operators and model definitions also carry modeling choices. '
           'See [scope and unspecified symbols](formalization-status.md#assumptions-and-unspecified-symbols).', '',
           'Omissions in this historical snapshot include covariant assembly and a connection, Noether currents, full-matrix spectra, physical fluid and wave PDE derivations, '
           'variational/action/path integrals, integer quantization, spinor representations, and gauge structures. '
           'The [current section scope map](formalization-status.md#section-by-section-status) separately tracks later changes. '
           'Numbering in old Lean comments is not used as mapping evidence.', '',
           '## Subsection navigation', '',
           '| Manuscript section | First page | Equation/claim coverage |', '|---|---:|---|']
    for sec in sections:
        covered = [str(r['id']) for r in rows if r['section'] == sec['id'] or ('.' not in sec['id'] and r['section'].startswith(sec['id']+'.'))]
        display = ', '.join(covered) if covered else 'See explicit unnumbered-topic entries and the section scope map; no numbered equation in this heading.'
        md.append(f'| {esc(sec["id"]+" "+sec["title"])} | {sec["page"]} | {display} |')
    for main in range(1,17):
        selected = [r for r in rows if int(r['section'].split('.')[0]) == main]
        md += ['', f'## Manuscript section {main}', '', '| Equation / claim | Page | Status | Lean declarations | Exact scope and essential premises |', '|---|---:|---|---|---|']
        for row in selected:
            names = '<br>'.join(f'[`{n.removeprefix("AsymmetricTensor.")}`](equation-baseline-source.lean.txt#L{lookup[n]["source_line"]})' for n in row['declarations']) or '—'
            label = f'[{row["id"]}]({row["pdf_url"]}) {row["topic"]}'
            md.append(f'| {esc(label)} | {row["page"]} | {row["status"]} | {names} | {esc(row["note"])} |')
    md += ['', '## Reproduction and stale-evidence guard', '',
           'On the current repository, validate the historical archives and deterministic artifacts explicitly:', '',
           '```sh', 'python3 scripts/equation_ledger.py --check --historical',
           'python3 -m unittest discover -s tests -p "test_equation_ledger.py"', '```', '',
           '`--historical` checks the archived source, dependency manifest and [audit program](equation-baseline-axiom-audit.lean.txt) against the original accepted hashes. '
           'It still checks the live manuscript and toolchain against their accepted hashes. '
           'It neither installs the archived manifest nor changes the current dependency selection. '
           'This is historical evidence only, not current-source coverage. The default live-source `--check` intentionally fails '
           'when the current source or manifest differs from the reviewed snapshot.', '',
           'The current production declarations can be inspected separately with the current committed dependencies:', '',
           '```sh', 'lake build AsymmetricTensor',
           'lake env lean tests/EquationAxioms.lean > /tmp/current-equation-axioms.log', '```', '',
           'That current-source log must not overwrite the historical audit. Historical mode rejects `--audit-log`. '
           'To independently reproduce the archived kernel audit, use a separate checkout whose live source, manifest, '
           'PDF, toolchain and audit program all match the accepted snapshot hashes, then run the Lean audit and '
           '`python3 scripts/equation_ledger.py --audit-log /tmp/equation-axioms.log --check` there. '
           'Never replace the current repository manifest to make the old ledger pass.', '',
           '`--check` also works without `--audit-log` in a matching snapshot checkout to check the committed audit and deterministic artifacts. '
           '`pdftotext` (Poppler) is required. `--write --historical` can regenerate presentation from the preserved reviewed evidence; '
           'it does not update the accepted hashes or reclassify equations for current code. '
           'A changed evidence source, PDF, toolchain, manifest or audit program fails rather than silently inheriting prior coverage claims. '
           'For a new current-source ledger, manually review equation mappings and hypotheses, update snapshot hashes, rebuild, '
           'rerun the full audit, and regenerate; do not mechanically copy these historical statuses.', '']
    return result, '\n'.join(md)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--audit-log', type=Path)
    p.add_argument('--historical', action='store_true', help='Validate archived #9/#33 source, manifest and audit evidence, not current production coverage')
    mode = p.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = p.parse_args()
    if args.historical and args.audit_log:
        raise ValueError('Historical mode checks committed baseline evidence only; reproduce a new kernel audit in a checkout whose live source matches the baseline')
    mapping = json.loads((ROOT/'docs/equation-map.json').read_text())
    verify_snapshot(ROOT, mapping['snapshot'], historical=args.historical)
    verify_archives(ROOT, mapping['snapshot'])
    archived = ROOT/ARCHIVED_FILES['AsymmetricTensor.lean']
    source = (archived if args.historical else ROOT/'AsymmetricTensor.lean').read_text()
    if args.audit_log:
        audit = audit_from_log(args.audit_log.read_text(), source, mapping['snapshot'])
    else:
        audit = json.loads((ROOT/'docs/declaration-audit.json').read_text())
    inventory, sections = equation_inventory(ROOT/'papers/asymmetric-metric-tensor.pdf')
    result, md = render(mapping, inventory, sections, audit, source)
    artifacts = {'docs/declaration-audit.json': canonical(audit),
                 'docs/equation-coverage.json': canonical(result), 'docs/equation-coverage.md': md}
    for path, expected in artifacts.items():
        if args.write:
            (ROOT/path).write_text(expected)
        elif not (ROOT/path).exists() or (ROOT/path).read_text() != expected:
            raise ValueError(f'Stale generated artifact: {path}; review and regenerate with --write')
    print(('HISTORICAL ARCHIVE ONLY: ' if args.historical else 'LIVE SOURCE: ') + f'Verified {len(inventory)} numbered equations, {len(result["entries"])-len(inventory)} unnumbered claims, '
          f'{audit["declaration_count"]} audited declarations; source/PDF/toolchain/manifest/audit hashes match.')

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as e:
        print(f'Equation ledger validation failed: {e}', file=sys.stderr)
        sys.exit(1)
