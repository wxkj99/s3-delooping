#!/usr/bin/env python3
"""Read-only lexical audit, NOT a proof certificate or typechecker; no Agda runs.
Agda.* compiler builtins and the kernel are excluded. Uses deps' lexical graph;
no semantic/elaboration checks, option-inheritance analysis, or vendor hash lock verification.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
import configure
import deps

UNSAFE = set(('allow-unsolved-metas allow-incomplete-matches no-termination-check '
              'no-positivity-check type-in-type omega-in-omega injective-type-constructors '
              'no-universe-check').split())
UNSAFE = {'--' + flag for flag in UNSAFE}
BENIGN = {'--lossy-unification', '--no-import-sorts', '-WnoUnsupportedIndexedMatch', '--guardedness'}
FORBIDDEN = {'TERMINATING', 'NON_TERMINATING', 'NO_POSITIVITY_CHECK', 'REWRITE'}
ROOTS = {'DeloopS3.Assembly.Complete', 'DeloopS3.HPInf.Complete'}
STRING = r'"(?:\\[\s\S]|[^"\\])*"|\'(?:\\.|[^\'\\\n])\''
HOLE = r'\{![\s\S]*?(?:!\}|$)'


def mask(text, options=False):
    """Preserve offsets; retain active pragma bodies separately; nest comments."""
    out, pragmas, end = list(text), [], 0
    comment = r'--(?=\s|$)[^\n]*' if options else r'--[^\n]*'
    for m in re.finditer(STRING + '|' + HOLE + '|' + comment + r'|\{-', text):
        start = m.start()
        if start < end:
            continue
        end = m.end()
        if text.startswith('{!', start):
            continue
        if text.startswith('{-#', start) and not options:
            end = text.find('#-}', start + 3)
            if end < 0:
                raise ValueError('unterminated pragma')
            pragmas.append((start + 3, text[start + 3:end]))
            end += 3
        elif text.startswith('{-', start):
            depth = 1
            for n in re.finditer(r'\{-|-\}', text[start + 2:]):
                depth += 1 if n.group() == '{-' else -1
                if depth == 0:
                    end = start + 2 + n.end()
                    break
            if depth:
                raise ValueError('unterminated block comment')
        out[start:end] = ['\n' if c == '\n' else ' ' for c in text[start:end]]
    return ''.join(out), pragmas


def scan(text, path, library=False):
    result = {k: [] for k in ('findings', 'benign_options', 'options', 'pragmas')}
    def emit(bucket, kind, token, pos):
        line = text.count('\n', 0, pos) + 1
        result[bucket].append(dict(kind=kind, token=token, path=str(path), line=line,
                                   evidence=text.splitlines()[line - 1]))
    if library:
        bodies = [(m.start() + 6, m.group()[6:]) for m in re.finditer(
            r'(?m)^flags:[^\n]*(?:\n[ \t]+[^\n]*)*', text)]
        code = ''
    else:
        code, bodies = mask(text)
    for offset, body in bodies:
        tokens = list(re.finditer(r'\S+', mask(body, options=True)[0]))
        if not tokens:
            continue
        name = 'OPTIONS' if library else tokens[0].group()
        if not library:
            emit('pragmas', 'pragma', name, offset + tokens[0].start())
            if name in FORBIDDEN:
                emit('findings', 'pragma', name, offset + tokens[0].start())
        if name == 'OPTIONS' or library:
            for token in tokens if library else tokens[1:]:
                flag, pos = token.group(), offset + token.start()
                emit('options', 'option', flag, pos)
                if flag.split('=', 1)[0] in UNSAFE:
                    emit('findings', 'option', flag, pos)
                if flag in BENIGN:
                    emit('benign_options', 'option', flag, pos)
    for m in re.finditer(HOLE + r'|(?<![^\s(){};])(?:postulate|\?)(?![^\s(){};])', code):
        kind = 'postulate' if m.group() == 'postulate' else 'hole'
        emit('findings', kind, 'postulate' if kind == 'postulate' else m.group()[:2], m.start())
    return result


def audit(project):
    project = project.resolve()
    report = dict(ok=False, note=__doc__, errors=[], roots=[], scanned_sources=[], libraries=[],
                  excluded_compiler_builtins=[], findings=[], benign_options=[], options=[], pragmas=[])
    def absorb(text, path, library=False):
        for key, values in scan(text, path, library).items():
            report[key].extend(values)
    try:
        graph = deps.audit(project, external=True)
        report['roots'] = graph['roots']
        report['excluded_compiler_builtins'] = graph['compiler_builtins']
        if not graph['ok']:
            report['graph_errors'] = {k: v for k, v in graph.items() if v and any(
                term in k for term in ('missing', 'unresolved', 'unknown', 'mismatch', 'violation', 'errors', 'during_audit'))}
            raise ValueError('dependency graph failed; closure not certified complete even lexically')
        configure.require(set(graph['roots']) == ROOTS, 'expected exactly both final roots')
        report['closure_counts'] = dict(local=len(graph['reachable']), vendored=len(graph['external']['reachable']))
        lock = configure.load_json(project / 'deps.lock.json')
        vendor = (project / configure.text(lock['cubical'], 'path')).resolve()
        configure.require(str(vendor) == graph['external']['directory'], 'vendor graph path differs from lock')
        libraries = [(lock['project'], project, configure.relative(configure.text(lock['project'], 'library_file'))),
                     (lock['cubical'], vendor, 'cubical.agda-lib')]
        for obj, base, name in libraries:
            path = (base / name).resolve()
            configure.require(path.is_relative_to(base), f'library path escapes locked directory: {path}')
            flags = configure.declaration(path).get('flags', [])
            matches = flags == configure.flags(obj)
            report['libraries'].append(dict(path=str(path), flags=flags, lock_flags_match=matches))
            absorb(path.read_text(encoding='utf-8'), path, True)
            if not matches:
                report['errors'].append(f'library flags differ from lock: {path}')
        modules = graph['modules'] | graph['external']['modules']
        for name in graph['transitive_modules']:
            if name.startswith('Agda.'):
                continue
            meta = modules[name]
            path = (project / meta['path']).resolve()
            raw = path.read_bytes()
            configure.require(hashlib.sha256(raw).hexdigest() == meta['sha256'], f'source changed: {path}')
            absorb(raw.decode('utf-8'), path)
            report['scanned_sources'].append(str(path))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        report['errors'].append(str(exc))
    report['counts'] = dict(sources=len(report['scanned_sources']), findings=len(report['findings']),
                            forbidden_by_kind=dict(Counter(x['kind'] for x in report['findings'])),
                            benign_options=len(report['benign_options']), pragmas=len(report['pragmas']),
                            options=len(report['options']), libraries=len(report['libraries']))
    report['ok'] = not (report['errors'] or report['findings'])
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--json', action='store_true')
    args = parser.parse_args(argv)
    report = audit(args.project)
    print(json.dumps(report, ensure_ascii=False, indent=2 if args.json else None))
    return 0 if report['ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
