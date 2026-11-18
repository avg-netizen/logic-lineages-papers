from pathlib import Path
import re,json
root=Path('.')
seen=set()
def visit(m):
 if m in seen:return
 p=root/(m.replace('.','/')+'.lean')
 if not p.exists():return
 seen.add(m)
 for x in re.findall(r'(?m)^(?:public )?import (LogicLineages\.[\w.]+)',p.read_text()):visit(x)
for m in ['LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemUndecidabilityProof','LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10BridgeProof']:visit(m)
missing=[m for m in sorted(seen) if not (root/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')).exists()]
print(json.dumps({'read_only':True,'roots':['SystemUndecidabilityProof','H10BridgeProof'],'local_modules':len(seen),'missing_standard_olean':missing,'note':'Existence inventory only, not source-hash/cache validity or proof acceptance.'},indent=2))
