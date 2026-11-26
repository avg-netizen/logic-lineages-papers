from pathlib import Path
import json, subprocess, sys, gzip, time
r=Path('/workspace/scratch/d6452c0f74c7/formalization-continuation-20261113/formalization');p=r/'verification/continuation-2026-11-13/bounded-evidence-verifier'; old=r/'verification/continuation-2026-11-13/recovery-object-and-history/runs/20261113T161501.862534Z'
report=json.loads((old/'REPORT.json').read_text());ax=json.loads((old/'AXIOMS.json').read_text());inh=json.loads((old/'INHERITED-PRESERVATION.json').read_text())
cmd=[sys.executable,str(p/'verify_evidence_bounded.py'),'--base',inh['baseline_commit'],'--frozen-file',str(old.parents[1]/'FROZEN-SHA256SUMS')]
for g in report['gate_roots']:cmd+=['--gate',g]
for a in ax['required_exact_aliases']:cmd+=['--alias',a]
for a in inh['allowed_mutable_paths']:
 if a!='formalization/AGENTS.md':cmd+=['--allow-inherited',a]
(p/'VALIDATION-COMMAND.json').write_text(json.dumps(cmd,indent=2)+'\n')
t=time.monotonic();result=subprocess.run(cmd,cwd=r,capture_output=True,text=True)
(p/'VALIDATION-STDOUT.txt').write_text(result.stdout);(p/'VALIDATION-STDERR.txt').write_text(result.stderr)
(p/'VALIDATION-EXECUTION.json').write_text(json.dumps({'returncode':result.returncode,'seconds':time.monotonic()-t},indent=2)+'\n')
print(result.stdout,result.stderr,flush=True)
if not result.stdout.strip():sys.exit(1)
new=r/json.loads(result.stdout)['report'];new=new.parent
with gzip.open(old/'SOURCE-AND-OBJECTS.json.gz','rt') as f: a=json.load(f)
with gzip.open(new/'SOURCE-AND-OBJECTS.json.gz','rt') as f: b=json.load(f)
am={x['module']:x for x in a};bm={x['module']:x for x in b}; differences=[]
for m in sorted(am.keys()|bm.keys()):
 x,y=am.get(m),bm.get(m)
 if x!=y:
  fields=[k for k in set(x or {})|set(y or {}) if (x or {}).get(k)!=(y or {}).get(k)]
  differences.append({'module':m,'fields':sorted(fields),'old_receipt':(x or {}).get('receipt'),'new_receipt':(y or {}).get('receipt'),'source_equal':(x or {}).get('source_sha256')==(y or {}).get('source_sha256'),'objects_equal':(x or {}).get('objects')==(y or {}).get('objects'),'log_equal':(x or {}).get('log_sha256')==(y or {}).get('log_sha256')})
newax=json.loads((new/'AXIOMS.json').read_text());nr=json.loads((new/'REPORT.json').read_text())
compare={'old_snapshot':str(old.relative_to(r)),'new_snapshot':str(new.relative_to(r)),'old_modules':len(a),'new_modules':len(b),'identical_rows':sum(am.get(m)==y for m,y in bm.items()),'differences':differences,'axioms_exact_equal':ax==newax,'frozen_exact_equal':json.loads((old/'FROZEN-PRESERVATION.json').read_text())==json.loads((new/'FROZEN-PRESERVATION.json').read_text()),'inherited_exact_equal':inh==json.loads((new/'INHERITED-PRESERVATION.json').read_text()),'profile_equal':report['native_profile']==nr['native_profile'],'gates_equal':report['gate_roots']==nr['gate_roots'],'required_aliases_equal':ax['required_exact_aliases']==newax['required_exact_aliases'],'new_errors':nr['errors']}
(p/'SNAPSHOT-COMPARISON.json').write_text(json.dumps(compare,indent=2)+'\n'); print(json.dumps({k:v for k,v in compare.items() if k!='differences'},indent=2))
