import ctypes,pathlib,json,sys,re,concurrent.futures,threading,time,subprocess,hashlib,urllib.request,urllib.error
BASE=pathlib.Path('/workspace/scratch/95d226e72a26/toolchain')
ROOT=pathlib.Path('/workspace/scratch/95d226e72a26/logic-lineages-papers/formalization')
PKG=ROOT/'.lake/packages';MATH=PKG/'mathlib';LEAN=BASE/'lean-4.32.0-rc1-linux'
lib=ctypes.CDLL(str(LEAN/'lib/lean/libleanshared.so'));lib.lean_initialize_runtime_module()
lib.lean_mk_string_from_bytes.argtypes=[ctypes.c_char_p,ctypes.c_size_t];lib.lean_mk_string_from_bytes.restype=ctypes.c_void_p
lib.lean_string_hash.argtypes=[ctypes.c_void_p];lib.lean_string_hash.restype=ctypes.c_uint64
lib.lean_uint64_mix_hash.argtypes=[ctypes.c_uint64,ctypes.c_uint64];lib.lean_uint64_mix_hash.restype=ctypes.c_uint64
lib.lean_dec_ref_cold.argtypes=[ctypes.c_void_p]
def sh(s):
 b=s.encode();p=lib.lean_mk_string_from_bytes(b,len(b));r=lib.lean_string_hash(p);lib.lean_dec_ref_cold(p);return r
def lh(v):
 r=7
 for a in v:r=lib.lean_uint64_mix_hash(r,a)
 return r
rootHash=lh([4]+[sh((MATH/f).read_text()) for f in ['lakefile.lean','lean-toolchain','lake-manifest.json']]);assert rootHash==0x4cc6b9c393376069
prefix={'Mathlib':'mathlib','Archive':'mathlib','Counterexamples':'mathlib','MathlibTest':'mathlib','Batteries':'batteries','BatteriesRecycling':'batteries','Aesop':'aesop','Cli':'Cli','ImportGraph':'importGraph','LeanSearchClient':'LeanSearchClient','Plausible':'plausible','Qq':'Qq','ProofWidgets':'proofwidgets'}
def clean(t):
 result=[];i=depth=0
 while i<len(t):
  if t.startswith('/-',i):depth+=1;i+=2;result.append('  ')
  elif depth and t.startswith('-/',i):depth-=1;i+=2;result.append('  ')
  elif not depth and t.startswith('--',i):
   e=t.find('\n',i)
   if e<0:break
   result.append('\n');i=e+1
  else:result.append(t[i] if not depth or t[i]=='\n' else ' ');i+=1
 return ''.join(result)
imports=re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',re.M)
memo={};sources={};deps={}
def get(mod):
 if mod in memo:return memo[mod]
 path=PKG/prefix[mod.split('.')[0]]/(mod.replace('.','/')+'.lean');t=path.read_text()
 ds=[x for line in imports.findall(clean(t)) for x in line.split() if x.split('.')[0] in prefix]
 hs=[get(d) for d in ds]
 ph=lh([sh(x) for x in (mod.replace('.','/')+'.lean').split('/')]);h=lh([rootHash,ph,sh(t)]+hs)
 memo[mod]=h;sources[mod]=str(path);deps[mod]=ds;return h
roots=sys.argv[1:] or (BASE/'upstream-roots.txt').read_text().splitlines()
for mod in roots:get(mod)
cache=BASE/'ltar';cache.mkdir(exist_ok=True)
print('root',f'{rootHash:016x}','modules',len(memo),flush=True)
(BASE/'CACHE-HASHES.json').write_text(json.dumps({'root_hash':f'{rootHash:016x}','modules':{m:f'{h:016x}' for m,h in memo.items()}},indent=2)+'\n')
urls=['https://lakecache.blob.core.windows.net/mathlib4-master/f/','https://lakecache.blob.core.windows.net/mathlib4/f/']
failed=[]
for attempt,url in enumerate(urls):
 pending=[(m,h) for m,h in memo.items() if not (cache/f'{h:016x}.ltar').is_file()]
 if not pending:break
 conf=[]
 for m,h in pending:
  conf.extend(['url = "'+url+f'{h:016x}.ltar"','output = "'+str(cache/f'{h:016x}.ltar.part')+'"','fail','location','silent','show-error','retry = 2','max-time = 40','write-out = "%{filename_effective}\\t%{http_code}\\t%{exitcode}\\n"','next'])
 cfg=BASE/'curl-acquire.conf';cfg.write_text('\n'.join(conf[:-1])+'\n')
 result=subprocess.run(['curl','--parallel','--parallel-max','16','--config',str(cfg)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 statuses={}
 for line in result.stdout.splitlines():
  columns=line.split('\t')
  if len(columns)==3:statuses[columns[0]]=(columns[1],columns[2])
 for m,h in pending:
  part=cache/f'{h:016x}.ltar.part'
  if statuses.get(str(part))==('200','0') and part.is_file() and part.stat().st_size:part.replace(cache/f'{h:016x}.ltar')
  else:part.unlink(missing_ok=True)
 print('download pass',attempt+1,'pending',sum(not (cache/f'{h:016x}.ltar').is_file() for m,h in memo.items()),flush=True)
failed=[m for m,h in memo.items() if not (cache/f'{h:016x}.ltar').is_file()]
if failed:
 (BASE/'CACHE-FAILURES.json').write_text(json.dumps(failed,indent=2));print('failed',failed,flush=True);sys.exit(1)
config=[{'file':str(cache/f'{h:016x}.ltar'),'base':str(MATH if prefix[m.split('.')[0]]=='mathlib' else ROOT)} for m,h in memo.items()]
conf=BASE/'extract.json';conf.write_text(json.dumps(config))
result=subprocess.run([str(LEAN/'bin/leantar'),'--jobs','1','-x','-j','-'],input=json.dumps(config),text=True,cwd=ROOT,check=True)
missing=[]
for m in memo:
 path=PKG/prefix[m.split('.')[0]]/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
 if not path.is_file():missing.append(str(path))
provenance={'root_hash':f'{rootHash:016x}','requested_roots':roots,'cache_archives':len(memo),'archive_bytes':sum((cache/f'{h:016x}.ltar').stat().st_size for h in memo.values()),'missing_expected_oleans':missing,'lean_archive_sha256':hashlib.file_digest((BASE/'lean-4.32.0-rc1-linux.tar.zst').open('rb'),'sha256').hexdigest(),'cache_hash_algorithm':'Pinned Cache.Hashing.lean implemented with exported pinned lean_string_hash and lean_uint64_mix_hash through ctypes; root hash matches recorded checkpoint','extractor':'Pinned leantar 0.1.19, one worker','source_revisions':{p['name']:p['revision'] for p in json.loads((BASE/'SOURCE-RESTORATION.json').read_text())['packages']},'upstream_compiler_invocations':0,'local_compiler_invocations':0}
(BASE/'ACQUISITION.json').write_text(json.dumps(provenance,indent=2)+'\n');print('complete',len(memo),'missing',missing,flush=True)
assert not missing
