#!/usr/bin/env python3
"""Read-only recursive native evidence verifier. Never launches Lean or Lake.
Derived from local-two-sol-2026-11-13/P12/verify_packet.py; adds input keys,
nested-comment scanning, explicit compiler-prefix validation and named audits.
"""
import argparse, hashlib, importlib.util, json, os, pathlib, re
ROOT=pathlib.Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('fixed_checker',ROOT/'scripts/check.py')
checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
p=argparse.ArgumentParser();p.add_argument('gate',nargs='+');p.add_argument('--out',required=True)
p.add_argument('--compiler',required=True);p.add_argument('--compiler-prefix',required=True)
p.add_argument('--fresh',action='store_true');p.add_argument('--require-audit',action='append',default=[])
a=p.parse_args()
profile={'heap_cap_mib':2048,'rss_cap_mib':1536,'wall_seconds':180,'cpu_seconds':90,'minimum_free_mib':2048,'core_only_profile':False,'single_thread':True,'threads':1,'upstream_cache_only':True}
seen={};errors=[];audits={};order=[];visiting=set();deps={};external={}
def clean(text):
 out=[];i=depth=0
 while i<len(text):
  if text.startswith('/-',i):depth+=1;out.append('  ');i+=2
  elif depth and text.startswith('-/',i):depth-=1;out.append('  ');i+=2
  elif not depth and text.startswith('--',i):
   end=text.find('\n',i)
   if end<0:break
   out.append('\n');i=end+1
  else:out.append(text[i] if not depth or text[i]=='\n' else ' ');i+=1
 return ''.join(out)
def discover(m):
 if m in seen:return
 if m in visiting:raise ValueError('import cycle: '+m)
 src=checker.source_for(m)
 if src is None:raise ValueError('missing local source: '+m)
 visiting.add(m);code=clean(src.read_text());deps[m]=[];external[m]=[]
 if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b',code,re.M):raise ValueError('forbidden source: '+m)
 for imp in checker.IMPORT.findall(code):
  for d in imp.split():
   if checker.source_for(d) is not None:deps[m].append(d);discover(d)
   else:external[m].append(d)
 seen[m]={'source':str(src),'source_sha256':checker.file_digest(src)}
 visiting.remove(m);order.append(m)
for gate in a.gate:discover(gate)
packages=ROOT/'.lake/packages'
if not packages.is_dir():packages=checker.CALCULATOR/'.lake/packages'
search=[checker.BUILD,ROOT]
if not a.fresh:search.append(checker.CALCULATOR/'.lake/build/lib/lean')
search.extend(x/'.lake/build/lib/lean' for x in sorted(packages.iterdir()) if x.is_dir())
lean_path=os.pathsep.join(str(x.resolve()) for x in search)
compiler=pathlib.Path(a.compiler).resolve();prefix=pathlib.Path(a.compiler_prefix).resolve()
context={'compiler':str(compiler),'compiler_sha256':checker.file_digest(compiler),'lean_path':lean_path,'pins':{},'external_objects':{}}
# Match the fixed checker's ELF selection context without executing its probe.
if compiler.read_bytes()[:4]==b'\x7fELF':
 if compiler != prefix/'bin/lean':raise ValueError('ELF compiler/prefix mismatch')
 context['selected_compiler']=checker.file_digest(prefix/'bin/lean');search.append(prefix/'lib/lean')
for root in (ROOT,checker.CALCULATOR):
 for name in ('lean-toolchain','lake-manifest.json','lakefile.toml','lakefile.lean'):
  path=root/name;context['pins'][str(path)]=checker.file_digest(path)
for m in sorted({x for ds in external.values() for x in ds}):
 relative=pathlib.Path(m.replace('.','/')+'.olean')
 obj=next((x/relative for x in search if (x/relative).is_file()),None)
 if obj is None:raise ValueError('missing external object: '+m)
 context['external_objects'][m]=checker.object_bundle(obj)
for m in order:
 try:
  src=checker.source_for(m);target=checker.BUILD/(m.replace('.','/')+'.olean')
  entry=json.loads(target.with_suffix('.checked.json').read_text());row=entry['native_row']
  if entry['schema']!=1 or row.get('module')!=m or row.get('returncode')!=0:raise ValueError('invalid native row/schema')
  if row['source_sha256']!=seen[m]['source_sha256']:raise ValueError('source mismatch')
  if entry['native_profile']!=profile:raise ValueError('profile mismatch')
  if not target.is_file() or entry['outputs']!=checker.object_bundle(target):raise ValueError('output bundle mismatch')
  objects=[]
  for d in deps[m]:
   obj=checker.BUILD/(d.replace('.','/')+'.olean')
   if not obj.is_file() and d.startswith('R1Calculator'):obj=checker.CALCULATOR/'.lake/build/lib/lean'/(d.replace('.','/')+'.olean')
   if not obj.is_file():raise ValueError('missing dependency: '+d)
   objects.append(obj)
  ctx={**context,'external_objects':{d:context['external_objects'][d] for d in external[m]}}
  key=checker.checked_input_key(src,objects,ctx)
  if key!=entry['input_key']:raise ValueError('input-key mismatch')
  log=ROOT/row['log'];log_hash=checker.file_digest(log)
  if log_hash is None or log_hash!=entry['log_sha256']:raise ValueError('log mismatch')
  rp=pathlib.Path(entry['native_receipt']);receipt=json.loads(rp.read_text())
  if any(receipt.get(k)!=v for k,v in profile.items()):raise ValueError('receipt profile mismatch')
  if row not in receipt.get('modules',[]):raise ValueError('native row absent from receipt')
  seen[m].update(input_key=key,outputs=entry['outputs'],native_receipt=str(rp),receipt_sha256=checker.file_digest(rp),log=str(log),log_sha256=log_hash)
  if 'Continuation20261114' in m:
   content=log.read_text()
   if re.search(r'sorry|forbidden axiom|error:',content,re.I):raise ValueError('failure/placeholder in new log')
   named=dict(re.findall(r'AXIOMS ([\w.]+): \[([^\]]*)\]',content))
   passes=re.findall(r'AXIOM_AUDIT_PASS ([\w.]+): (\d+) theorems',content)
   for name,axs in named.items():
    if any(ax.strip() not in {'propext','Classical.choice','Quot.sound'} for ax in axs.split(',') if ax.strip()):raise ValueError('nonstandard axioms: '+name)
    audits[name]=[x.strip() for x in axs.split(',') if x.strip()]
   for ns,count in passes:
    if sum(n==ns or n.startswith(ns+'.') for n in named)!=int(count):raise ValueError('audit count mismatch: '+ns)
   expected=re.findall(r'^\s*#audit_namespace\s+([\w.]+)',clean(src.read_text()),re.M)
   if any(ns not in {x[0] for x in passes} for ns in expected):raise ValueError('missing declared namespace audit')
 except (OSError,KeyError,ValueError,TypeError) as e:errors.append({'module':m,'error':str(e)})
for name in a.require_audit:
 if name not in audits:errors.append({'required_audit':name,'error':'missing named standard-only audit'})
report={'gates':a.gate,'status':'verified' if not errors else 'failed','native_source_matched_modules':len(seen),'errors':errors,'new_named_standard_axioms':audits,'compiler_context':context,'modules':seen,'limits':'Focused closure only. Does not certify paper correspondence or a full-root build. Imported axioms are certified through actual new named declaration closures.'}
pathlib.Path(a.out).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('gates','status','native_source_matched_modules','errors','new_named_standard_axioms')},indent=2));raise SystemExit(bool(errors))
