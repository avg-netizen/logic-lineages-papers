#!/usr/bin/env python3
"""Read-only check. Does not apply a patch, compile, stage, commit or publish."""
from pathlib import Path
import sys,json,hashlib
here=Path(__file__).resolve().parent
m=json.loads((here/'REVIEW.json').read_text())
if len(sys.argv)!=2:raise SystemExit('Usage: verify_application.py INTEGRATION_REPO')
r=Path(sys.argv[1]).resolve();missing=[];changed=[]
for p,h in {**m['base_files_sha256'],**m['supplier_files_sha256']}.items():
 q=r/p
 if not q.is_file():missing.append(p)
 elif hashlib.sha256(q.read_bytes()).hexdigest()!=h:changed.append(p)
if missing or changed:
 print(json.dumps({'ready':False,'missing_count':len(missing),'changed_count':len(changed),'missing':missing,'changed':changed},indent=2))
 print('Do not apply yet. Integrate missing suppliers unchanged; rebase if register/audit bytes changed. If only SHA256SUMS changed from authorized supplier integration, apply the metadata-only patch after separately verifying all metadata and supplier hashes, then regenerate the combined checksum file. No integration gate/root-inclusion claim is inferred from this static check.')
 raise SystemExit(1)
print('Static hashes pass. Coordinator must still confirm independent acceptance, aggregate/root inclusion and successful integration before applying. Expected status counts: 162 checked, 2 inherited, 25 pending / 189.')
