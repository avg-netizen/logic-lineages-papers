from pathlib import Path
import sys,json,hashlib,shutil
F=Path('/workspace/scratch/d6452c0f74c7/formalization-resume-20261120/formalization');D=F/'verification/new-paper-set-2026-11-18/paper16/recovery-nov19';sys.path.insert(0,str(D))
from replay_owner_ready_core_evidence import owner,exporter,cloud_context
receipt=F/'build-reports/1795198659399128987-11.json';v=json.loads(receipt.read_text());ns='LogicLineages.PersistentMarking.';root=ns+'NumberedWindowConcretePositiveEndpointsChecks';assert v['requested']==[root];assert all(x['module'].startswith(ns) for x in v['modules']);owner.compiler_context=cloud_context
fr=D/'NUMBERED-WINDOW-CONCRETE-POSITIVE-ENDPOINTS-FROZEN.json';au=D/'NUMBERED-WINDOW-CONCRETE-POSITIVE-ENDPOINTS-AUTHOR-MANIFEST.json';a=json.loads(au.read_text());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert a['required_frozen_sha256']==h(fr);pins={}
for ps in [json.loads(fr.read_text())['sources'],a['sources'],a['required_accepted_supplier_records']]:
 assert all(h(F.parent/p)==s for p,s in ps.items());pins.update(ps)
assert len(pins)==51
report=owner.verify(receipt,['NumberedWindowConcretePositiveEndpointsChecks.'+x for x in a['expected_audit_aliases']],[fr]);report['frozen_sources']=pins
out=exporter.export(report);dest=D/'NUMBERED-WINDOW-CONCRETE-POSITIVE-ENDPOINTS-CLOUD-EVIDENCE-20261120.json'
assert not dest.exists()
dest.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],out['local_modules'],out['exact_aliases'],len(out['source_pins']),h(dest))
