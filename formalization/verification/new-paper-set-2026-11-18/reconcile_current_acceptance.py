import pathlib,json,hashlib,datetime
r=pathlib.Path(__file__).resolve().parents[3];f=r/'formalization';p=f/'verification/new-paper-set-2026-11-18';cache={}
def digest(x):
 x=pathlib.Path(x)
 if x not in cache:cache[x]=hashlib.sha256(x.read_bytes()).hexdigest() if x.is_file() else None
 return cache[x]
rows=[];unique=set()
for path in sorted((p/'accepted').glob('*.json')):
 a=json.loads(path.read_text());ev=p/a['evidence'];d=json.loads(ev.read_text());row={'id':a['id'],'evidence':a['evidence'],'evidence_hash_matches':digest(ev)==a['evidence_sha256'],'source_drift':[],'artifact_drift':[],'receipt_or_log_drift':[]}
 mods=d['modules']; entries=mods.items() if isinstance(mods,dict) else ((x['module'],x) for x in mods)
 count=0
 for name,m in entries:
  count+=1;unique.add(name);src=pathlib.Path(m.get('source',f/(name.replace('.','/')+'.lean')))
  if digest(src)!=m['source_sha256']:row['source_drift'].append(name)
  for fn,h in m['outputs'].items():
   if digest(fn)!=h:row['artifact_drift'].append(fn)
  for key,hkey in [('native_receipt','receipt_sha256'),('log','log_sha256')]:
   if hkey in m and digest(m[key])!=m[hkey]:row['receipt_or_log_drift'].append(m[key])
 row['modules']=count;rows.append(row)
assert rows
errors=[x for x in rows if not x['evidence_hash_matches'] or x['source_drift'] or x['artifact_drift'] or x['receipt_or_log_drift']]
report={'status':'verified' if not errors else 'drift','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'acceptances':len(rows),'unique_local_modules':len(unique),'unique_hashed_paths':len(cache),'rows':rows,'errors':errors}
(p/'ACCEPTANCE-CURRENT-RECONCILIATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))
