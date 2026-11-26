#!/usr/bin/env python3
"""Read-only reconciliation of twelve actual free-covariance modules against native receipts."""
import hashlib, importlib.util, json, os, pathlib, re, shutil
HERE=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'scripts/check.py').is_file())
REPO=ROOT.parent
sp=importlib.util.spec_from_file_location('checker',ROOT/'scripts/check.py')
c=importlib.util.module_from_spec(sp);sp.loader.exec_module(c)
profile={'heap_cap_mib':1536,'rss_cap_mib':512,'wall_seconds':180,'cpu_seconds':90,
 'minimum_free_mib':768,'core_only_profile':True,'single_thread':True,'threads':1,'upstream_cache_only':True}
env=os.environ.copy()
search=[c.BUILD,ROOT,c.CALCULATOR/'.lake/build/lib/lean']
search.extend(p/'.lake/build/lib/lean' for p in sorted((ROOT/'.lake/packages').iterdir()) if p.is_dir())
env['LEAN_PATH']=os.pathsep.join(str(p.resolve()) for p in search)
compiler='/workspace/scratch/d6452c0f74c7/toolchains/lean-4.32.0-rc1-linux/bin/lean'
prefix=pathlib.Path(compiler).parent.parent
context={'compiler':compiler,'compiler_sha256':c.file_digest(pathlib.Path(compiler)),'lean_path':env['LEAN_PATH'],'pins':{},'external_objects':{},'selected_compiler':c.file_digest(pathlib.Path(compiler))}
for root in (ROOT,c.CALCULATOR):
 for name in ('lean-toolchain','lake-manifest.json','lakefile.toml','lakefile.lean'):
  path=root/name; context['pins'][str(path)]=c.file_digest(path)
context['external_objects']['Init']=c.object_bundle(prefix/'lib/lean/Init.olean')
modules=['Syntax', 'SpineSyntax', 'SpineTyping', 'Signature', 'Occurrences', 'NameBridge', 'FreeSubstitution', 'SpineMarking', 'Comparison', 'ComparisonTargets', 'BridgeTargets', 'SpineTypingTargets', 'SpineShiftProof', 'SubstitutionTargets', 'InsertionTargets', 'SubstitutionProof', 'InsertionProof', 'SpineSubstitutionProof', 'OpeningFoundationProof', 'SpineMarkingTargets', 'SpineMarkingProof', 'ElementarySupportProof', 'ElementaryProof', 'ElementaryChecks', 'ElementaryBridgeTargets', 'ElementaryBridgeProof', 'ElementaryBridgeChecks']
errors=[];rows=[];axioms={};pins={}
for short in modules:
 module='LogicLineages.PersistentMarking.'+short
 source=c.source_for(module); target=c.BUILD/(module.replace('.','/')+'.olean')
 deps=[]
 for imp in c.IMPORT.findall(source.read_text()):
  for dep in imp.split():
   if c.source_for(dep):deps.append(c.BUILD/(dep.replace('.','/')+'.olean'))
 local_context={**context, "external_objects": context["external_objects"] if short=="Syntax" else {}}
 key=c.checked_input_key(source,deps,local_context)
 row=c.checked_cache_hit(target,key,profile)
 if row is None:errors.append('Missing input/output/source/profile-matched native receipt: '+module);continue
 if row['source_sha256']!=c.file_digest(source):errors.append('Source mismatch: '+module)
 log=(ROOT/row['log']).read_text()
 for name,body in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.M):
  ax=[a.strip() for a in body.split(',') if a.strip()];axioms[name]=ax
  if set(ax)-{'propext','Classical.choice','Quot.sound'}:errors.append('Forbidden axioms '+name)
 rows.append({'module':module,'source_sha256':c.file_digest(source),'native_row':row,'outputs':c.object_bundle(target)})
 pins[str(source.relative_to(REPO))]=c.file_digest(source)
for filename in ['COMPARATOR-FROZEN.json','ELEMENTARY-BRIDGE-FROZEN.json','TYPED-SPINE-FROZEN.json','SUBSTITUTION-FROZEN.json','INSERTION-FROZEN.json']:
 for source,digest in json.loads((HERE/filename).read_text())['sources'].items():
  if c.file_digest(REPO/source)!=digest:errors.append('Frozen source changed: '+source)
required={'ElementaryChecks':['strictIncluded','ordinaryReflexive'],'ElementaryBridgeChecks':['markEncoding']}
for module,names in required.items():
 for name in names:
  full='LogicLineages.PersistentMarking.'+module+'.'+name
  if full not in axioms:errors.append('Missing axiom log: '+full)
report={'status':'verified' if not errors else 'failed','local_modules':len(rows),'exact_aliases':len(axioms),'profile':profile,'errors':errors,'source_pins':pins,'axioms':axioms,'modules':rows,'context':context,'full_root_build':False,'CI':False}
(HERE/'INDEPENDENT-ELEMENTARY-EVIDENCE.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'local_modules':len(rows),'aliases':len(axioms),'errors':errors},indent=2))
raise SystemExit(bool(errors))
