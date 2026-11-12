#!/usr/bin/env python3
"""Restore exact pinned official Lean cache artifacts without compiling Lean.

Hash algorithm adapted from mathlib4 Cache/Hashing.lean (Apache-2.0),
Copyright (c) 2023 Arthur Paulino; authors Arthur Paulino and Jon Eugster.
Official source revision and SHA-256 checks below restrict this port to the
validated 4.32.0-rc1 snapshot. This is recovery tooling, not a proof checker.
"""
import argparse,ctypes,json,re,sys,urllib.request,concurrent.futures,subprocess,hashlib
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--formalization',type=Path,required=True,help='Repository formalization directory')
parser.add_argument('--toolchain',type=Path,required=True,help='Official extracted lean-4.32.0-rc1-linux directory')
parser.add_argument('--cache-dir',type=Path,required=True)
parser.add_argument('--workers',type=int,default=8)
parser.add_argument('--unpack',action='store_true',help='Extract using bundled leantar; do not run alongside compiler')
parser.add_argument('--hash-only',action='store_true',help='Compute hashes only; no download or unpack')
parser.add_argument('modules',nargs='*',default=['Mathlib'])
args=parser.parse_args()
if not 1<=args.workers<=32:parser.error('--workers must be between 1 and 32')
FORM=args.formalization.resolve();TC=args.toolchain.resolve();OUT=args.cache_dir.resolve();PK=FORM/'.lake/packages'
EXPECTED_SOURCES={'Cache/Hashing.lean': 'ff055315fdd39801121892aea6eb1b52e44c47aebbaadbc3a668e9ea4da8006e', 'Cache/IO.lean': 'cc5f3f8a86c0670816dd5fb8e731e473eba07560a15aa7b6552d947fe3fcc33b', 'Cache/Infra.lean': 'b31ecd55a8af1867e8a8f9a6ddb71bb8a8eb8e354ff9d0dbb20faeb190f893e8', 'Cache/Requests.lean': '52615687c58f6ddeed971e0be3ad9ecfd3e8ad8342226b9cb09c25f088b2268f'}
if (FORM/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.32.0-rc1':raise RuntimeError('Unexpected toolchain pin')
manifest=json.loads((FORM/'lake-manifest.json').read_text())
for package in manifest['packages']:
 if package['type']=='git':
  got=subprocess.check_output(['git','-C',str(PK/package['name']),'rev-parse','HEAD'],text=True).strip()
  if got!=package['rev']:raise RuntimeError('Dependency pin mismatch: '+package['name'])
if subprocess.check_output(['git','-C',str(PK/'mathlib'),'rev-parse','HEAD'],text=True).strip()!='360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56':raise RuntimeError('Unsupported mathlib pin')
for name,digest in EXPECTED_SOURCES.items():
 if hashlib.sha256((PK/'mathlib'/name).read_bytes()).hexdigest()!=digest:raise RuntimeError('Official cache source mismatch: '+name)
version=subprocess.check_output([str(TC/'bin/lean'),'--version'],text=True)
if '4.32.0-rc1' not in version or 'b4812ae53eea93439ad5dce5a5c26591c31cb697' not in version:raise RuntimeError('Unexpected official runtime version')
OUT.mkdir(parents=True,exist_ok=True)
lib=ctypes.CDLL(str(TC/'lib/lean/libleanshared.so'));lib.lean_initialize_runtime_module();lib.lean_mk_string.argtypes=[ctypes.c_char_p];lib.lean_mk_string.restype=ctypes.c_void_p;lib.lean_string_hash.argtypes=[ctypes.c_void_p];lib.lean_string_hash.restype=ctypes.c_uint64;lib.lean_uint64_mix_hash.argtypes=[ctypes.c_uint64,ctypes.c_uint64];lib.lean_uint64_mix_hash.restype=ctypes.c_uint64
mix=lib.lean_uint64_mix_hash
def sh(s):return lib.lean_string_hash(lib.lean_mk_string(s.encode()))
def lh(xs):
 h=7
 for x in xs:h=mix(h,x)
 return h
root=lh([4]+[sh((PK/'mathlib'/n).read_text()) for n in ['lakefile.lean','lean-toolchain','lake-manifest.json']])
prefix={'Mathlib':'mathlib','Batteries':'batteries','BatteriesRecycling':'batteries','Aesop':'aesop','Cli':'Cli','ImportGraph':'importGraph','LeanSearchClient':'LeanSearchClient','Plausible':'plausible','Qq':'Qq','ProofWidgets':'proofwidgets','Archive':'mathlib','Counterexamples':'mathlib','MathlibTest':'mathlib'}
def clean(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 return ''.join(out)
cache={};rows={}
def calc(mod):
 if mod in cache:return cache[mod]
 parts=mod.split('.');path=PK/prefix[parts[0]]/('/'.join(parts)+'.lean');s=path.read_text();imports=[]
 for line in clean(s).splitlines():
  line=line.strip()
  if not line or line=='module' or line=='prelude':continue
  m=re.match(r'(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
  if not m:break
  imports.extend(x for x in m[1].split() if x.split('.')[0] in prefix)
 p=parts[:-1]+[parts[-1]+'.lean'];h=lh([root,lh(map(sh,p)),sh(s)]+[calc(x) for x in imports]);cache[mod]=h;rows[mod]={'hash':f'{h:016x}','source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'imports':imports,'package':prefix[parts[0]]};return h
for module in args.modules: calc(module)
if args.hash_only:
 print(json.dumps({'root_hash':f'{root:016x}','module_count':len(rows)}));sys.exit(0)
(OUT/'hashes.json').write_text(json.dumps({'root_hash':f'{root:016x}','modules':rows},indent=2));print('HASHED',len(rows),'root',f'{root:016x}',flush=True)
def download(item):
 mod,row=item;dest=OUT/(row['hash']+'.ltar')
 # Re-download from the official endpoint rather than trusting an unvalidated local file.
 for container in ['mathlib4-master','mathlib4']:
  url=f"https://lakecache.blob.core.windows.net/{container}/f/{dest.name}"
  try:
   with urllib.request.urlopen(url,timeout=45) as response:data=response.read()
   temporary=dest.with_suffix('.part');temporary.write_bytes(data);temporary.replace(dest);return mod,url
  except Exception as e:last=str(e)
 return mod,'ERROR:'+last
with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
 results=list(pool.map(download,rows.items()))
(OUT/'download-provenance.json').write_text(json.dumps(results,indent=2));bad=[x for x in results if x[1].startswith('ERROR')];print('DOWNLOADED',len(results)-len(bad),'FAIL',len(bad),bad[:3],flush=True)
if bad:sys.exit(1)
if args.unpack:
 config=[{'file':str(OUT/(row['hash']+'.ltar')),'base':str(PK/'mathlib')} if mod.split('.')[0]=='Mathlib' else str(OUT/(row['hash']+'.ltar')) for mod,row in rows.items()]
 subprocess.run([str(TC/'bin/leantar'),'-x','--jobs','1','-j','-'],input=json.dumps(config),text=True,cwd=FORM,check=True)
 missing=[mod for mod,row in rows.items() if not (PK/row['package']/'.lake/build/lib/lean'/('/'.join(mod.split('.'))+'.olean')).is_file()]
 if missing:raise RuntimeError(f'Missing unpacked artifacts: {missing[:20]}')
(OUT/'artifact-digests.json').write_text(json.dumps({mod:hashlib.sha256((OUT/(row['hash']+'.ltar')).read_bytes()).hexdigest() for mod,row in rows.items()},indent=2))
print('READY',len(rows),'official artifacts; no compiler invoked',flush=True)
