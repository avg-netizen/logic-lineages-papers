#!/usr/bin/env python3
"""Reproduce a source-content index from a Git baseline, without compiling Lean.
Outputs canonical JSON to --output and its SHA256 to stdout. The output is an
inventory, not evidence that any theorem was compiled or independently audited.
"""
import argparse,hashlib,json,pathlib,subprocess
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',required=True,type=pathlib.Path)
p.add_argument('--commit',required=True)
p.add_argument('--output',required=True,type=pathlib.Path)
a=p.parse_args()
def git(*args,**kw):return subprocess.check_output(['git','-C',str(a.repo),*args],**kw)
commit=git('rev-parse',a.commit+'^{commit}').decode().strip()
entries=git('ls-tree','-rz',commit,'--','formalization','04-pure-r1-calculator/lean').split(b'\0')
selected=[]
config={'formalization/TARGETS.json','formalization/lean-toolchain','formalization/lake-manifest.json','formalization/lakefile.toml'}
for entry in entries:
 if not entry:continue
 metadata,path=entry.split(b'\t',1);name=path.decode();mode,kind,obj=metadata.split()
 if kind==b'blob' and (name.endswith('.lean') or name in config):selected.append((name,obj))
raw=git('cat-file','--batch',input=b'\n'.join(obj for _,obj in selected)+b'\n');offset=0;files={}
for name,obj in selected:
 end=raw.index(b'\n',offset);head=raw[offset:end].split();size=int(head[2]);start=end+1
 assert head[0]==obj and head[1]==b'blob'
 files[name]=hashlib.sha256(raw[start:start+size]).hexdigest();offset=start+size+1
value={'schema':'git-baseline-source-index-v1','commit':commit,'files':files}
data=json.dumps(value,sort_keys=True,separators=(',',':')).encode()+b'\n'
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(data)
print(json.dumps({'files':len(files),'sha256':hashlib.sha256(data).hexdigest(),'tree':git('rev-parse',commit+'^{tree}').decode().strip()}))
