#!/usr/bin/env python3
"""Read-only archive and source-register verification; never invokes Lean."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
a=ROOT/'archive/comparison-editions-pre-2026-11-17'
m=json.loads((a/'MANIFEST.json').read_text())
for x in m['files']:
 for key in ('archived_path','original_path'):
  p=ROOT/x[key]
  assert p.is_file() and digest(p)==x['sha256'],str(p)
d=json.loads((ROOT/'formalization/CURRENT-COMPARISON-TARGETS.json').read_text())
ids=set();count=0
for p in d['papers']:
 found={}
 for source in p['source_files']:
  f=ROOT/source['path'];assert digest(f)==source['sha256'],str(f)
  s=f.read_text()
  for match in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}',s,re.S):
   kind,body=match.groups();label=re.search(r'\\label\{([^}]+)\}',body)
   assert label,source['path']
   key=f"{p['paper']}:{label[1]}";assert key not in found,key
   found[key]=(kind,body.strip(),s[:match.start()].count('\n')+1,source['path'])
 assert len(found)==p['numbered_statement_count']
 for row in p['statements']:
  assert row['id'] not in ids;ids.add(row['id'])
  assert found[row['id']]==(row['kind'],row['statement_latex'],row['line'],row['file'])
 count+=len(found)
assert count==d['numbered_statement_count']
if 'status_counts' in d:
 from collections import Counter
 assert dict(Counter(x['status'] for p in d['papers'] for x in p['statements']))==d['status_counts']
# Acceptance/register integrity only. Native recursive verifiers and independent
# scope reviews remain required; this index check does not replace either.
verification=Path(__file__).resolve().parent
accepted={};accepted_ids=set();accepted_total=0
for f in sorted((verification/'accepted').glob('*.json')):
 record=json.loads(f.read_text());accepted_total+=1
 assert record['id'] not in accepted_ids,record['id']
 accepted_ids.add(record['id'])
 assert (verification/record['independent_review']).is_file(),str(f)
 assert digest(verification/record['evidence'])==record['evidence_sha256'],str(f)
 for source,sha in record.get('source_pins',{}).items():
  assert digest(ROOT/source)==sha,source
 if record['kind']=='current numbered statement':
  key=record['statement'];assert key not in accepted,key
  accepted[key]=(f,record)
 else:
  assert record['kind']=='supporting only',str(f)
  assert not record.get('numbered_promotions',[]),str(f)
checked={row['id']:row for paper in d['papers'] for row in paper['statements'] if row['status']=='checked'}
assert checked.keys()==accepted.keys(),'checked/acceptance bijection'
for key,row in checked.items():
 f,record=accepted[key]
 assert ROOT/'formalization'/row['acceptance']==f,key
 assert row['formal_target']==record['target'],key
 assert row['verified_alias']==record['exact_alias'],key
print(json.dumps({'accepted_packets':accepted_total,'checked_numbered_statements':len(checked),'archive_files_verified' :len(m['files']),'current_source_statements':count,'unique_ids':len(ids),'errors':[]},indent=2))
