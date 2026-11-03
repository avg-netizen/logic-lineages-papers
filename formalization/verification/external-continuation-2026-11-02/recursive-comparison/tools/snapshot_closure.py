import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--repo',required=True);p.add_argument('--output',required=True);p.add_argument('modules',nargs='+');a=p.parse_args();R=Path(a.repo).resolve();F=R/'formalization';C=R/'04-pure-r1-calculator/lean';P=F/'.lake/packages'
imp=re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$',re.M)
def clean(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2;out.append('  ')
  elif depth and s.startswith('-/',i):depth-=1;i+=2;out.append('  ')
  elif not depth and s.startswith('--',i):
   j=s.find('\n',i)
   if j<0:break
   out.append('\n');i=j+1
  else:out.append(s[i] if not depth or s[i]=='\n' else ' ');i+=1
 return ''.join(out)
def source(m):
 base=C if m=='R1Calculator' or m.startswith('R1Calculator.') else F
 q=base/(m.replace('.','/')+'.lean')
 return q if q.is_file() else None
rows={};up=set()
def visit(m):
 if m in rows:return
 q=source(m)
 if q is None:up.add(m);return
 deps=[x for line in imp.findall(clean(q.read_text())) for x in line.split()]
 rows[m]=dict(module=m,path=str(q.relative_to(R)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),imports=deps)
 for d in deps:visit(d)
for m in a.modules:visit(m)
local=[rows[m] for m in sorted(rows)];bindings={str(q.relative_to(R)):hashlib.sha256(q.read_bytes()).hexdigest() for q in [F/'lean-toolchain',F/'lake-manifest.json',F/'scripts/check.py']}
d=dict(schema='closure-snapshot-v1',requested=a.modules,files=local,upstream_imports=sorted(up),bindings=bindings)
d['closure_sha256']=hashlib.sha256(json.dumps(d,sort_keys=True,separators=(',',':')).encode()).hexdigest();Path(a.output).write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(dict(local_modules=len(local),upstream_imports=len(up),closure_sha256=d['closure_sha256'])))
