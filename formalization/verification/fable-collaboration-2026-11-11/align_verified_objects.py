"""Migrate the pre-refresh, source-matched native snapshot into checked hash stamps.
Only byte-identical saved objects are reused. Newly refreshed foundational modules
must instead have successful current native rows and current source/dependency times.
No Lean proof source or binary bytes are changed.
"""
import fcntl,gzip,hashlib,importlib.util,json,os,shutil
from pathlib import Path
from datetime import datetime,timezone
root=Path.cwd();here=root/'verification/fable-collaboration-2026-11-11'
def loadmod(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
check=loadmod('cache_checker',root/'scripts/check.py')
evidence=loadmod('cache_evidence',here/'verify_evidence.py').verifier
locks=[]
for name in ['logic-lineages-papers-lean.lock','pure-r1-calculator-lean.lock']:
 f=(check.shared_lock_directory()/name).open('a');fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);locks.append(f)
assert json.loads((root/'.local-run-policy.json').read_text())['paused']
original=here/'runs/20261111T213142.473648Z'
report=json.loads((original/'REPORT.json').read_text())
assert all(s.startswith('Missing source-matched native row: ') for s in report['errors'])
missing={s.split(': ',1)[1] for s in report['errors']}
old={r['module']:r for r in json.loads(gzip.decompress((original/'SOURCE-AND-OBJECTS.json.gz').read_bytes()))}
order,deps,external=evidence.closure(json.loads((here/'GATES.json').read_text()))
assert set(order)==set(old)|missing
receipt_path=root/'build-reports/1794432927456596723-10.json';receipt=json.loads(receipt_path.read_text())
assert all(receipt.get(k)==v for k,v in evidence.PROFILE.items())
fresh={r['module']:r for r in receipt['modules'] if r.get('returncode')==0}
validated={};rows=[]
# Validate every source, binary bundle and successful proof log before touching
# any timestamp. The pre-refresh snapshot checked source/dependency freshness;
# its only errors were the fifteen historical resource-profile mismatches.
for module in order:
 source=check.source_for(module);target=check.BUILD/(module.replace('.','/')+'.olean')
 objects=check.object_bundle(target)
 assert all(v is not None for v in objects.values()),module
 if module in old:
  saved=old[module];assert check.file_digest(source)==saved['source_sha256'],module
  assert {str(Path(p).relative_to(root)):v for p,v in objects.items()}==saved['objects'],module
  row=saved['native_row'];native_receipt=root/saved['receipt']
  assert check.file_digest(root/row['log'])==saved['log_sha256'],module
  native=json.loads(native_receipt.read_text())
  assert row in native['modules'] and all(native.get(k)==v for k,v in evidence.PROFILE.items()),module
  origin='byte-identical-pre-refresh-snapshot'
 else:
  row=fresh[module];assert check.file_digest(source)==row['source_sha256'],module
  native_receipt=receipt_path
  inputs=[source]+[check.BUILD/(d.replace('.','/')+'.olean') for d in deps[module]]
  assert all(p.is_file() and p.stat().st_mtime_ns<=target.stat().st_mtime_ns for p in inputs),module
  origin='current-successful-native-refresh'
 assert row['returncode']==0 and (root/row['log']).is_file(),module
 validated[module]=(row,native_receipt)
 rows.append({'module':module,'source_sha256':check.file_digest(source),'origin':origin,
              'objects':{str(Path(p).relative_to(root)):v for p,v in objects.items()},
              'receipt':str(native_receipt.relative_to(root)),'native_row':row,
              'log_sha256':check.file_digest(root/row['log'])})
# Metadata refresh uses topological dependency order, as checked_cache_hit does.
# Outputs are known native bytes; timestamp churn alone need not rebuild proofs.
changed=[]
for module in order:
 target=check.BUILD/(module.replace('.','/')+'.olean');source=check.source_for(module)
 inputs=[source]+[check.BUILD/(d.replace('.','/')+'.olean') for d in deps[module]]
 newest=max(p.stat().st_mtime_ns for p in inputs)
 if newest>target.stat().st_mtime_ns:
  for name in check.object_bundle(target):
   p=Path(name);s=p.stat();os.utime(p,ns=(s.st_atime_ns,max(s.st_mtime_ns,newest)))
  changed.append(module)
packages=root/'.lake/packages'
if not packages.is_dir():packages=check.CALCULATOR/'.lake/packages'
search=[check.BUILD,root,check.CALCULATOR/'.lake/build/lib/lean']
search += [p/'.lake/build/lib/lean' for p in sorted(packages.iterdir()) if p.is_dir()]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(str(p.resolve()) for p in search),LEAN_NUM_THREADS='1')
context=check.checked_compiler_context(shutil.which('lean'),env,set(external))
for module in order:
 source=check.source_for(module);target=check.BUILD/(module.replace('.','/')+'.olean')
 imported=[check.BUILD/(d.replace('.','/')+'.olean') for d in deps[module]]
 direct_external=[d for line in check.IMPORT.findall(evidence.clean_source(source.read_text())) for d in line.split() if check.source_for(d) is None]
 local={**context,'external_objects':{d:context['external_objects'][d] for d in direct_external}}
 key=check.checked_input_key(source,imported,local);row,native_receipt=validated[module]
 check.save_checked_cache(target,key,row,native_receipt,evidence.PROFILE)
 assert check.checked_cache_hit(target,key,evidence.PROFILE) is not None,module
out={'verified_modules':len(order),'byte_identical_snapshot_modules':len(old),'current_native_refresh_modules':len(missing),
     'timestamp_refresh_modules':len(changed),'seeded_hash_stamps':len(order),'native_proof_compilations':0,'compiler_metadata_probe':True,
     'original_snapshot':str(original.relative_to(root)), 'timestamp_only_changes':True,
     'run_utc':datetime.now(timezone.utc).isoformat()}
(here/'VERIFIED-CACHE-MIGRATION.json').write_text(json.dumps(out,indent=2)+'\n')
with gzip.open(here/'CACHE-MIGRATION-SOURCE-AND-OBJECTS.json.gz','wt') as stream:json.dump(rows,stream,sort_keys=True)
print(json.dumps(out))
