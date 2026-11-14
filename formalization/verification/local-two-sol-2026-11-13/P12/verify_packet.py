#!/usr/bin/env python3
"""Read-only source/native/log/receipt evidence for focused exact gates."""
import argparse, hashlib, importlib.util, json, pathlib, re
ROOT=pathlib.Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('fixed_checker',ROOT/'scripts/check.py')
checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
parser=argparse.ArgumentParser();parser.add_argument('gate');parser.add_argument('--out',required=True);args=parser.parse_args()
profile={'heap_cap_mib':2048,'rss_cap_mib':1536,'wall_seconds':180,'cpu_seconds':90,'minimum_free_mib':2048,'core_only_profile':False,'single_thread':True,'threads':1,'upstream_cache_only':True}
seen={};errors=[];audits=[]
def visit(module):
 if module in seen:return
 source=checker.source_for(module)
 if source is None:return
 seen[module]={'source':str(source.relative_to(ROOT)) if source.is_relative_to(ROOT) else str(source),'source_sha256':checker.file_digest(source)}
 text=source.read_text();clean=re.sub(r'/\-.*?\-/','',text,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 deps=[]
 for imports in checker.IMPORT.findall(clean):
  for dep in imports.split():
   if checker.source_for(dep) is not None:deps.append(dep);visit(dep)
 target=checker.BUILD/(module.replace('.','/')+'.olean')
 try:
  entry=json.loads(target.with_suffix('.checked.json').read_text());row=entry['native_row']
  if row.get('returncode')!=0:raise ValueError('nonzero native row')
  if row['source_sha256']!=seen[module]['source_sha256']:raise ValueError('source hash mismatch')
  if entry['native_profile']!=profile:raise ValueError('profile mismatch')
  if entry['outputs']!=checker.object_bundle(target):raise ValueError('output bundle mismatch')
  log=ROOT/row['log']
  if checker.file_digest(log)!=entry['log_sha256']:raise ValueError('native log hash mismatch')
  receipt_path=pathlib.Path(entry['native_receipt']);receipt=json.loads(receipt_path.read_text())
  if any(receipt.get(k)!=v for k,v in profile.items()):raise ValueError('receipt profile mismatch')
  if row not in receipt['modules']:raise ValueError('native row absent from receipt')
  seen[module].update(native_receipt=str(receipt_path),log=row['log'],log_sha256=entry['log_sha256'],object_sha256=checker.file_digest(target))
  if 'TwoSol20261113' in module:
   content=log.read_text();audits.extend(re.findall(r'AXIOM_AUDIT_PASS [^\n]+',content))
   if 'sorry' in content.lower():raise ValueError('placeholder warning in log')
 except (OSError,KeyError,ValueError,TypeError) as error:errors.append({'module':module,'error':str(error)})
visit(args.gate)
report={'gate':args.gate,'native_source_matched_modules':len(seen),'errors':errors,'new_namespace_audits':audits,'modules':seen,'meaning':'Focused gate input-key checks establish import/compiler context; this independent evidence rechecks source/output/log/receipt hashes and fixed native profiles.'}
pathlib.Path(args.out).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'gate':args.gate,'native_source_matched_modules':len(seen),'errors':errors,'new_namespace_audits':audits},indent=2));raise SystemExit(bool(errors))
