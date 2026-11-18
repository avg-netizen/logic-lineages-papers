import sys,importlib.util,os,re,json,pathlib
spec=importlib.util.spec_from_file_location('checker',str(pathlib.Path('scripts/check.py').resolve()));c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
order=[];deps={};ext={};all_ext=set()
def visit(m):
 if m in deps:return
 p=c.source_for(m)
 if p is None:return
 text=p.read_text(); code=[]; i=0; depth=0
 while i<len(text):
  if text.startswith('/-',i): depth+=1;code.append('  ');i+=2
  elif depth and text.startswith('-/',i):depth-=1;code.append('  ');i+=2
  elif not depth and text.startswith('--',i):
   end=text.find('\n',i)
   if end<0:break
   code.append('\n');i=end+1
  else:code.append(text[i] if not depth or text[i]=='\n' else ' ');i+=1
 text=''.join(code)
 ds=[d for line in c.IMPORT.findall(text) for d in line.split()];deps[m]=[d for d in ds if c.source_for(d)];ext[m]=[d for d in ds if not c.source_for(d)];all_ext.update(ext[m])
 for d in deps[m]:visit(d)
 order.append(m)
visit('LogicLineages.StandardControlCurrent.PolynomialBooleanStatementChecks')
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(str(x.resolve()) for x in [c.BUILD,c.ROOT,c.CALCULATOR/'.lake/build/lib/lean',*[p/'.lake/build/lib/lean' for p in sorted((c.ROOT/'.lake/packages').iterdir()) if p.is_dir()]])
compiler='/workspace/scratch/d6452c0f74c7/toolchains/lean-4.32.0-rc1-linux/bin/lean';ctx=c.checked_compiler_context(compiler,env,all_ext)
profile={'heap_cap_mib':2048,'rss_cap_mib':1536,'wall_seconds':180,'cpu_seconds':90,'minimum_free_mib':2048,'core_only_profile':False,'single_thread':True,'threads':1,'upstream_cache_only':True}
miss=set();rows=[]
for m in order:
 target=c.BUILD/(m.replace('.','/')+'.olean'); ps=[c.BUILD/(d.replace('.','/')+'.olean') for d in deps[m]]
 mc={**ctx,'external_objects':{d:ctx['external_objects'][d] for d in ext[m]}}
 hit=c.checked_cache_hit(target,c.checked_input_key(c.source_for(m),ps,mc),profile)
 if not hit:miss.add(m)
 closure=set()
 def collect(n):
  if n in closure:return
  closure.add(n)
  for d in deps[n]:collect(d)
 collect(m)
 rows.append({'module':m,'closure':len(closure),'uncached':len(closure&miss),'hit':bool(hit)})
print(json.dumps({'total':len(order),'misses':len(miss),'candidates':[r for r in rows if not r['hit'] and 30<=r['uncached']<=50]},indent=2))
pathlib.Path('verification/new-paper-set-2026-11-18/paper18/BOOLEAN-SOLVER-INVENTORY.json').write_text(json.dumps(rows,indent=2)+'\n')
