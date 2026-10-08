"""Rebuild the exact final endpoint closure without any old project objects."""
from pathlib import Path
import argparse
import ast
import concurrent.futures
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

D = Path(__file__).resolve().parent
B = D.parents[3]
E = D.parent
ACCEPTED = E / 'entropy197500-final-independent'
BASE = B / 'work/clean-replay-cb65148'
PRIOR = B / 'work/full1744-song-audit'
SRC = D / 'clean-lean'
LIB = SRC / '.lake/build/lib/lean'
LOGS = D / 'logs'
LEAN = Path('/Users/avatar/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean')
FLAGS = ['-j1', '-M12288', '-t0', '-DmaxSynthPendingDepth=3']

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def read(p):
    return json.loads(Path(p).read_text())

def write(p, data):
    p = Path(p)
    tmp = p.with_name(p.name + '.tmp')
    tmp.write_text(json.dumps(data, indent=2) + '\n')
    tmp.replace(p)

def rel(m):
    return Path(*m.split('.'))

def imports(text):
    # All project headers use one module per import line. Comments are stripped first.
    return re.findall(r'(?m)^\s*(?:public\s+)?import[ \t]+([\w.]+)', text)

def source_scanner():
    p = B / 'outputs/kls-verification/scripts/verify.py'
    node = next(n for n in ast.parse(p.read_text()).body
                if isinstance(n, ast.FunctionDef) and n.name == 'code_without_comments_or_strings')
    ns = {}
    exec(compile(ast.Module(body=[node], type_ignores=[]), '<accepted-source-scanner>', 'exec'), ns)
    return ns['code_without_comments_or_strings']

def check_accepted():
    assert sha(ACCEPTED / 'receipt.json') == 'b9dbc476960c2093b088faa983d5be5e46e8a46df59738d9bdcb4f1301af2e89'
    assert sha(ACCEPTED / 'evidence-sha256.json') == 'f227cc6b563c70addad87e35f72576f3d816f7314ec525041c4a3c072f047442'
    all_roots = [ACCEPTED]
    for spec in read(ACCEPTED / 'accepted-dependency-paths.json'):
        p = Path(spec['path'])
        assert sha(p / 'receipt.json') == spec['receipt_sha256']
        assert sha(p / 'evidence-sha256.json') == spec['evidence_sha256']
        assert read(p / 'receipt.json')['success']
        all_roots.append(p)
    evidence_count = 0
    for p in all_roots:
        for f, v in read(p / 'evidence-sha256.json').items():
            assert sha(p / f) == v, (p, f)
            evidence_count += 1
    si = read(ACCEPTED / 'baseline-source-inventory.json')
    bi = read(ACCEPTED / 'baseline-module-artifacts.json')
    sides = read(ACCEPTED / 'baseline-sidecars.json')
    for f, v in si.items():
        assert sha(BASE / f) == v, f
    for m, e in bi.items():
        assert sha(BASE / 'lean' / rel(m).with_suffix('.lean')) == e['source_sha256'], m
        assert sha(BASE / 'lean/.lake/build/lib/lean' / rel(m).with_suffix('.olean')) == e['object_sha256'], m
        assert sha(BASE / 'evidence/source-rebuild' / (m + '.log')) == e['log_sha256'], m
    for f, e in sides.items():
        assert sha(BASE / 'lean/.lake/build/lib/lean' / f) == e['sha256'], f
    packages = read(ACCEPTED / 'dependency-pins.json')
    for e in packages:
        p = Path(e['resolved_checkout'])
        assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=p, text=True).strip() == e['revision']
        assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=p, text=True).strip()
    assert sha(LEAN) == 'd1d9c26a539f54fe839d2aa7760bf1ac1dd76a30b26e2c9684bebf2900038fcf'
    return {'success': True, 'accepted_packet_roots': len(all_roots),
            'accepted_evidence_files': evidence_count, 'baseline_modules': len(bi),
            'baseline_source_and_config_pins': len(si), 'baseline_sidecars': len(sides),
            'package_pins': len(packages), 'compiler_sha256': sha(LEAN)}

def prepare():
    assert not SRC.exists(), 'Use a new audit directory rather than overwriting a rebuild.'
    check = check_accepted()
    bi = read(ACCEPTED / 'baseline-module-artifacts.json')
    selected = read(ACCEPTED / 'selected-origin-paths.json')
    owners = {m: BASE / 'lean' / rel(m).with_suffix('.lean') for m in bi}
    owners.update({m: Path(p) / rel(m).with_suffix('.lean') for m, p in selected.items()})
    owners['Entropy197500FullVerification'] = ACCEPTED / 'Entropy197500FullVerification.lean'
    owners['CheegerTwoReverification'] = D / 'cheeger-review/CheegerTwoReverification.lean'
    owners['FinalKLS500'] = D / 'FinalKLS500.lean'
    scan = source_scanner()
    deps = {m: imports(scan(p.read_text())) for m, p in owners.items()}
    closure = set()
    def visit(m):
        if m in closure or m not in owners:
            return
        closure.add(m)
        for dep in deps[m]:
            visit(dep)
    visit('FinalKLS500')
    assert len(closure) == 1699
    SRC.mkdir()
    LIB.mkdir(parents=True)
    LOGS.mkdir()
    provenance = {}
    source_scans = []
    for m in sorted(closure):
        p = owners[m]
        code = scan(p.read_text())
        bad = re.findall(r'(?m)^\s*(?:axiom|constant)\s|\b(?:sorry|admit|native_decide|unsafe|implemented_by|run_cmd|run_elab|elab_rules|elab|macro_rules|macro)\b', code)
        assert not bad, (m, bad)
        target = SRC / rel(m).with_suffix('.lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, target)
        assert sha(p) == sha(target)
        provenance[m] = {'source': str(p), 'source_sha256': sha(p),
                         'copied_source': str(target), 'imports': deps[m],
                         'baseline': m in bi}
        source_scans.append({'module': m, 'forbidden_tokens': bad})
    for f in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        shutil.copyfile(BASE / 'lean' / f, SRC / f)
    packages = read(ACCEPTED / 'dependency-pins.json')
    external_paths = [str(Path(e['resolved_checkout']) / '.lake/build/lib/lean') for e in packages]
    external_paths.append(str(LEAN.parent.parent / 'lib/lean'))
    paths = [str(LIB), *external_paths]
    external = {}
    for m in sorted(set.union(*(set(deps[m]) for m in closure)) - closure):
        obj = next((Path(p) / rel(m).with_suffix('.olean') for p in external_paths
                    if (Path(p) / rel(m).with_suffix('.olean')).is_file()), None)
        assert obj is not None, ('missing external import', m)
        external[m] = {str(q): sha(q) for q in obj.parent.glob(obj.name + '*') if q.is_file()}
    assert not any(LIB.rglob('*.olean'))
    manifest = {'success': True, 'source_modules': len(closure),
                'baseline_modules': sum(x['baseline'] for x in provenance.values()),
                'additional_modules': sum(not x['baseline'] for x in provenance.values()),
                'all_sources_byte_preserved': True, 'old_project_objects_in_search_path': False,
                'LEAN_PATH': paths, 'source_provenance': provenance,
                'external_direct_imports': external, 'flags': FLAGS,
                'max_concurrent_compilers': 4, 'compiler_sha256': sha(LEAN),
                'lean_version': subprocess.check_output([LEAN, '--version'], text=True).strip(),
                'accepted_input_check': check}
    write(D / 'prepare-receipt.json', manifest)
    write(D / 'source-scan.json', source_scans)
    print(json.dumps({k: manifest[k] for k in ['source_modules','baseline_modules','additional_modules','old_project_objects_in_search_path']}, indent=2), flush=True)

def verify_sources(manifest):
    for m, e in manifest['source_provenance'].items():
        assert sha(e['source']) == sha(e['copied_source']) == e['source_sha256'], m
    for objects in manifest['external_direct_imports'].values():
        for p, v in objects.items():
            assert sha(p) == v, p

def build():
    manifest = read(D / 'prepare-receipt.json')
    verify_sources(manifest)
    sources = manifest['source_provenance']
    assert not any(LIB.rglob('*.olean'))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(manifest['LEAN_PATH']),
               LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1')
    remaining, done, running, results = set(sources), set(), {}, []
    deps = {m: set(e['imports']) & sources.keys() for m,e in sources.items()}
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    failed = False
    def one(m):
        e = sources[m]
        source = SRC / rel(m).with_suffix('.lean')
        obj = LIB / rel(m).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        assert not obj.exists()
        assert sha(source) == e['source_sha256']
        logfile = LOGS / (m + '.log')
        cmd = [str(LEAN), *FLAGS, '-o', str(obj), str(source.relative_to(SRC))]
        start = time.monotonic()
        with logfile.open('w') as out:
            status = subprocess.run(cmd, cwd=SRC, env=env, stdout=out, stderr=subprocess.STDOUT).returncode
        text = logfile.read_text()
        artifacts = {str(q.relative_to(LIB)): sha(q) for q in obj.parent.glob(obj.name+'*') if q.is_file()}
        return {'module': m, 'command': cmd, 'exit_status': status,
                'seconds': round(time.monotonic()-start,3), 'fresh_object': True,
                'source_sha256': sha(source), 'artifacts': artifacts,
                'log': str(logfile), 'log_sha256': sha(logfile),
                'warnings': len(re.findall(r'(?m)^.*warning:', text)),
                'errors': len(re.findall(r'(?m)^.*error:', text))}
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        while remaining or running:
            ready = [] if failed else sorted(m for m in remaining if deps[m] <= done)
            for m in ready[:4-len(running)]:
                remaining.remove(m)
                running[pool.submit(one,m)] = m
            if not running:
                failed = bool(remaining) or failed
                break
            complete, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for f in complete:
                m = running.pop(f)
                e = f.result()
                results.append(e)
                if e['exit_status'] == 0:
                    done.add(m)
                else:
                    failed = True
                    print('FAILED',m,e['log'],flush=True)
            receipt = {'success': not failed and not remaining and not running,
                       'started_utc': started, 'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                       'completed': len(done), 'total': len(sources), 'results': results,
                       'unbuilt': sorted(remaining), 'running': sorted(running.values()),
                       'flags': FLAGS, 'max_concurrent_compilers':4,
                       'old_project_objects_imported':False,
                       'dependency_library_cache_reused':True,
                       'prepare_receipt_sha256':sha(D/'prepare-receipt.json')}
            write(D / 'build-receipt.json', receipt)
            if len(results)%25==0 or failed or not remaining and not running:
                print('BUILD',len(done),'/',len(sources),'failed',failed,flush=True)
    assert not failed and not remaining and len(done)==len(sources)
    verify_sources(manifest)
    write(D / 'post-build-input-check.json', check_accepted())
    print('CLEAN_FINAL_ENDPOINT_CLOSURE_BUILD_PASS',len(done),flush=True)

if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('action',choices=['prepare','build'])
    args=parser.parse_args()
    {'prepare':prepare,'build':build}[args.action]()
