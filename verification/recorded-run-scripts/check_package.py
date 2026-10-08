"""Check the portable configuration and entry against the sealed fresh objects."""
import os
from pathlib import Path
import shutil
import subprocess
import time
import tomllib
from rebuild import D, LIB, LEAN, FLAGS, ACCEPTED, sha, read, write

stage=D/'release-stage'
project=stage/'lean'
assert read(D/'final-verification-receipt.json')['review_status']=='accepted'
inventory=read(stage/'verification/portable-source-inventory.json')
assert len(inventory)==1712
for p,v in inventory.items():
    assert sha(stage/p)==v,p
modules={str(p.relative_to(project).with_suffix('')).replace(os.sep,'.')
         for p in project.rglob('*.lean')}
assert len(modules)==1712
config=tomllib.loads((project/'lakefile.toml').read_text())
library=config['lean_lib'][0]
assert config['defaultTargets']==['KLSFinal'] and library['name']=='KLSFinal'
assert len(library['roots'])==len(set(library['roots']))==1712
assert len(library['globs'])==len(set(library['globs']))==1712
assert set(library['roots'])==set(library['globs'])==modules
assert config['moreLeanArgs']==FLAGS
pins={n:sha(project/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
assert config['require'][0]['rev']=='4beb549110aa44b87d699166cece6e3642bddf34'
fresh_artifacts=read(D/'fresh-build-artifact-inventory.json')
for p,v in fresh_artifacts.items():
    assert sha(LIB/p)==v,p
temporary=project/'.lake'
assert not temporary.exists()
packages=temporary/'packages'
packages.mkdir(parents=True)
links=[]
for e in read(ACCEPTED/'dependency-pins.json'):
    p=packages/e['name']
    p.symlink_to(Path(e['resolved_checkout']),target_is_directory=True)
    links.append(p)
import_path=temporary/'build/lib/lean'
import_path.parent.mkdir(parents=True)
import_path.symlink_to(LIB,target_is_directory=True)
links.append(import_path)
env=dict(os.environ,LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1')
env.pop('LEAN_PATH',None)
commands=[[str(LEAN.parent/'lake'),'env','lean','--version'],
          [str(LEAN.parent/'lake'),'env','lean',*FLAGS,'FinalKLSRange.lean']]
results=[]
try:
    for index,cmd in enumerate(commands):
        start=time.monotonic()
        run=subprocess.run(cmd,cwd=project,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log=D/('portable-config-'+str(index)+'.log')
        log.write_text(run.stdout)
        results.append({'command':cmd,'exit_status':run.returncode,'seconds':round(time.monotonic()-start,3),
                        'log':str(log),'log_sha256':sha(log)})
        print(run.stdout,flush=True)
        assert run.returncode==0,(cmd,run.stdout)
        assert 'error:' not in run.stdout and 'warning:' not in run.stdout,(cmd,run.stdout)
        if index==0:
            assert '4.35.0-rc3' in run.stdout
finally:
    for link in links:
        assert link.is_symlink()
        link.unlink()
    shutil.rmtree(temporary)
assert not temporary.exists()
for p,v in inventory.items():
    assert sha(stage/p)==v,p
for p,v in pins.items():
    assert sha(project/p)==v,p
for p,v in fresh_artifacts.items():
    assert sha(LIB/p)==v,p
receipt={'success':True,'mathematical_modules':1710,'audit_modules':2,
         'lake_library_roots_and_globs_exactly_all_1712_sources':True,
         'portable_source_inventory_sha256':sha(stage/'verification/portable-source-inventory.json'),
         'package_configuration_sha256':pins,'commands':results,
         'entry_check_uses_only_the_previously_sealed_fresh_project_objects':True,
         'previous_project_object_directories_used':False,
         'all_temporary_links_removed':True,
         'all_1710_fresh_mathematics_artifacts_unchanged':True,
         'scope':'Configuration loading and an additional final-entry type check. The complete 1710-module fresh proof build is separately recorded; this is not a second complete Lake rebuild.',
         'check_runner_sha256':sha(D/'check_package.py')}
write(D/'portable-configuration-check.json',receipt)
shutil.copyfile(D/'portable-configuration-check.json',stage/'verification/portable-configuration-check.json')
for r in results:
    shutil.copyfile(r['log'],stage/'verification'/Path(r['log']).name)
shutil.copyfile(D/'check_package.py',stage/'verification/recorded-run-scripts/check_package.py')
print('PORTABLE_CONFIGURATION_AND_ENTRY_CHECK_PASSED',sha(D/'portable-configuration-check.json'),flush=True)
