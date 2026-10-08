from pathlib import Path
import json,os,subprocess,hashlib,time,sys
R=Path(__file__).resolve().parent;E=R.parent.parent/'entropy197500-final-independent';b=json.loads((E/'build-receipt.json').read_text());paths=[str(R),*b['LEAN_PATH']];env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in sys.argv[1:]:
 src=R/(name+'.lean');out=R/(name+'.olean');log=R/(name+'.log')
 cmd=['/Users/avatar/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean','-j1','-M16384','-t0','-o',str(out),str(src)]
 start=time.monotonic();begin=time.time_ns()
 with log.open('w') as f:p=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
 r={'command':cmd,'LEAN_PATH':paths,'exit_status':p.returncode,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'artifact_sha256':sha(out) if out.exists() else None,'fresh_artifact':out.exists() and out.stat().st_mtime_ns>=begin};(R/(name+'-build.json')).write_text(json.dumps(r,indent=2)+'\n');print(name,r['exit_status'],r['seconds']);print(log.read_text())
 if p.returncode:sys.exit(p.returncode)
