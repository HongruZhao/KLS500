"""Repair the new wrapper comment and freshly extend the proof closure by lower four."""
import copy
import datetime
import os
import re
import shutil
import subprocess
import time
from pathlib import Path
from rebuild import D, B, ACCEPTED, SRC, LIB, LOGS, LEAN, FLAGS
from rebuild import sha, read, write, rel, source_scanner, imports, verify_sources, check_accepted

# The original scheduler owns all 1699 jobs until it has no running worker.
while True:
    build = read(D/'build-receipt.json')
    failures = [e for e in build['results'] if e['exit_status']]
    assert all(e['module']=='FinalKLS500' for e in failures), failures
    if len(build['results'])==1699 and not build['running'] and not build['unbuilt']:
        break
    time.sleep(5)
assert build['completed']==1698 and len(failures)==1
assert not build['success']
assert not (D/'initial-build-receipt.json').exists()
shutil.copyfile(D/'build-receipt.json',D/'initial-build-receipt.json')
shutil.copyfile(D/'prepare-receipt.json',D/'initial-prepare-receipt.json')
shutil.copyfile(SRC/'FinalKLS500.lean',D/'initial-wrapper-source.lean')
shutil.copyfile(LOGS/'FinalKLS500.log',LOGS/'FinalKLS500.first-attempt.log')
initial = read(D/'prepare-receipt.json')
assert (SRC/'FinalKLS500.lean').read_text().replace(
    '/-- Final public endpoints, using the unchanged upstream OpenAI model. -/',
    '/- Final public endpoints, using the unchanged upstream OpenAI model. -/') == (D/'FinalKLS500.lean').read_text()
assert 'unexpected token' in (LOGS/'FinalKLS500.first-attempt.log').read_text()
for e in build['results']:
    assert sha(e['log'])==e['log_sha256']
    for p,v in e['artifacts'].items():
        assert sha(LIB/p)==v
assert not (LIB/'FinalKLS500.olean').exists()
shutil.copyfile(D/'FinalKLS500.lean',SRC/'FinalKLS500.lean')
repaired = copy.deepcopy(initial)
repaired['source_provenance']['FinalKLS500']['source_sha256']=sha(D/'FinalKLS500.lean')
repaired['initial_prepare_receipt_sha256']=sha(D/'initial-prepare-receipt.json')
repaired['new_wrapper_comment_repaired']=True
write(D/'prepare-receipt.json',repaired)
env=dict(os.environ,LEAN_PATH=os.pathsep.join(repaired['LEAN_PATH']),LEAN_NUM_THREADS='1',
         OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1')

def compile_one(m,source_sha):
    src=SRC/rel(m).with_suffix('.lean')
    obj=LIB/rel(m).with_suffix('.olean')
    assert sha(src)==source_sha and not obj.exists()
    obj.parent.mkdir(parents=True,exist_ok=True)
    log=LOGS/(m+'.log')
    cmd=[str(LEAN),*FLAGS,'-o',str(obj),str(src.relative_to(SRC))]
    start=time.monotonic()
    with log.open('w') as out:
        status=subprocess.run(cmd,cwd=SRC,env=env,stdout=out,stderr=subprocess.STDOUT).returncode
    text=log.read_text()
    e={'module':m,'command':cmd,'exit_status':status,'seconds':round(time.monotonic()-start,3),
       'fresh_object':True,'source_sha256':sha(src),
       'artifacts':{str(p.relative_to(LIB)):sha(p) for p in obj.parent.glob(obj.name+'*') if p.is_file()},
       'log':str(log),'log_sha256':sha(log),
       'warnings':len(re.findall(r'(?m)^.*warning:',text)),
       'errors':len(re.findall(r'(?m)^.*error:',text))}
    assert status==0,text
    print('FRESH',m,'PASS',flush=True)
    return e

result=compile_one('FinalKLS500',repaired['source_provenance']['FinalKLS500']['source_sha256'])
assert result['warnings']==0 and result['errors']==0
build['results']=[e for e in build['results'] if e['module']!='FinalKLS500']+[result]
build.update(success=True,completed=1699,prepare_receipt_sha256=sha(D/'prepare-receipt.json'),
             finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
             initial_failed_attempt_receipt_sha256=sha(D/'initial-build-receipt.json'),
             new_wrapper_comment_only_repair=True)
verify_sources(repaired)
post=check_accepted()
write(D/'post-build-input-check.json',post)
write(D/'build-receipt.json',build)
write(D/'wrapper-comment-repair.json',{
    'success':True,'scope':'Only a newly authored wrapper namespace comment was changed from a documentation comment to an ordinary block comment; all theorem statements and proof bodies are byte unchanged.',
    'initial_source_sha256':sha(D/'initial-wrapper-source.lean'),
    'repaired_source_sha256':sha(D/'FinalKLS500.lean'),
    'initial_prepare_receipt_sha256':sha(D/'initial-prepare-receipt.json'),
    'initial_build_receipt_sha256':sha(D/'initial-build-receipt.json'),
    'initial_failure_log_sha256':sha(LOGS/'FinalKLS500.first-attempt.log'),
    'repaired_compile':result,'accepted_mathematical_sources_changed':False})

plan=read(D/'range-review/addon-plan.json')
assert plan['success'] and plan['new_module_count']==11
assert plan['current_prepare_receipt_sha256']==sha(D/'initial-prepare-receipt.json')
effective=copy.deepcopy(repaired)
provenance=effective['source_provenance']
scan=source_scanner()
baseline=read(ACCEPTED/'baseline-module-artifacts.json')
ordered=plan['topological_addon_order']
assert len(ordered)==len(plan['modules'])==11
module_specs={e['module']:e for e in plan['modules']}
for m in ordered:
    e=module_specs[m]
    assert m not in provenance and sha(e['source'])==e['source_sha256']
    if e['baseline']:
        assert baseline[m]['source_sha256']==e['source_sha256']
    else:
        assert m=='FinalKLSRange' and e['source_sha256']=='91b032ab69d086ebd37d78c70a3d2acf93d01b34b0673cea41980c03bc692663'
    text=Path(e['source']).read_text()
    code=scan(text)
    assert not re.findall(r'(?m)^\s*(?:axiom|constant)\s|\b(?:sorry|admit|native_decide|unsafe|implemented_by|run_cmd|run_elab|elab_rules|elab|macro_rules|macro)\b',code)
    assert imports(code)==e['imports']
    target=SRC/rel(m).with_suffix('.lean')
    assert not target.exists()
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(e['source'],target)
    provenance[m]={'source':e['source'],'source_sha256':e['source_sha256'],
                   'copied_source':str(target),'imports':e['imports'],'baseline':e['baseline']}
for m, pins in plan['new_external_direct_import_pins'].items():
    effective['external_direct_imports'][m]={e['path']:e['sha256'] for e in pins}
effective.update(source_modules=1710,baseline_modules=1395,additional_modules=315,
                 repaired_base_prepare_receipt_sha256=sha(D/'prepare-receipt.json'),
                 addon_plan_sha256=sha(D/'range-review/addon-plan.json'))
write(D/'effective-prepare-receipt.json',effective)
verify_sources(effective)
done=set(repaired['source_provenance'])
extras=[]
for m in ordered:
    local={i for i in provenance[m]['imports'] if i in provenance}
    assert local<=done,(m,local-done)
    extras.append(compile_one(m,provenance[m]['source_sha256']))
    done.add(m)
assert len(done)==1710
verify_sources(effective)
post=check_accepted()
write(D/'effective-post-build-input-check.json',post)
combined=copy.deepcopy(build)
combined.update(success=True,completed=1710,total=1710,results=build['results']+extras,
                prepare_receipt_sha256=sha(D/'effective-prepare-receipt.json'),
                base_build_receipt_sha256=sha(D/'build-receipt.json'),
                addon_plan_sha256=sha(D/'range-review/addon-plan.json'),
                finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                original_sources_changed=False)
write(D/'effective-build-receipt.json',combined)
print('FRESH_FULL_CLOSURE_WITH_RANGE_LEMMA_PASS',1710,flush=True)
