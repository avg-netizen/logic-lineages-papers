#!/usr/bin/env python3
"""Read-only full conservative import-closure reconciliation against exact native receipts."""
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
compiler=shutil.which('lean'); assert compiler
context=c.checked_compiler_context(compiler,env,{'Init'})
modules=['Syntax', 'SpineSyntax', 'SpineTyping', 'Signature', 'NameBridge', 'FreeSubstitution', 'StructuralContext', 'Occurrences', 'SpineMarking', 'Comparison', 'StructuralStabilityTargets', 'StructuralCoverageTargets', 'TypeSupport', 'DecisionInventory', 'DecisionPorts', 'DecisionObservations', 'FiniteDomainFoundation', 'FiniteDomainFoundationTargets', 'FinitePrefixProof', 'FiniteDomainSchema', 'HereditaryDomainCode', 'HereditaryDomainSemantics', 'HereditaryDomainTargets', 'MarkedExtras', 'DecisionSourceUniverse', 'MarkedBaseTuples', 'MarkedFamilyParameters', 'MarkedFamilyCoding', 'MarkedFamilyCoherence', 'MarkedFamilyCoherenceTargets', 'MarkedBaseTupleTargets', 'FiniteEqualityProof', 'FiniteVectorProof', 'HereditaryLookupProof', 'HereditaryTupleProof', 'FiniteDomainSchemaTargets', 'DecisionPortsTargets', 'DecisionPortsProof', 'FiniteExtensionProof', 'FiniteSchemaExactProof', 'HereditaryConstructionProof', 'MarkedBaseTupleFoundationProof', 'MarkedExtrasTargets', 'HereditaryCoordinateProof', 'HereditaryCoordinateBoundsProof', 'HereditaryTupleRoundtripProof', 'HereditaryTupleAdapterProof', 'HereditaryTupleBoundsProof', 'HereditaryPrefixCodingProof', 'FiniteSchemaDistinctProof', 'HereditaryOutputProof', 'HereditarySemanticOutputProof', 'HereditaryNaturalityBridgeTargets', 'HereditaryTupleOrderProof', 'HereditaryTupleRestrictionProof', 'HereditaryDecodedValiditySupport', 'HereditaryOrderTargets', 'HereditaryOrderBitProof', 'HereditaryOrderTableProof', 'HereditaryCodeOrderProof', 'HereditaryEncodeCoordinateProof', 'HereditaryVectorRebuildProof', 'HereditaryCodeReconstructionProof', 'HereditaryEncodingCongruenceProof', 'HereditarySemanticOrderProof', 'HereditaryDecodedValidityProof', 'HereditaryOrderStepProof', 'HereditaryPartialOrderProof', 'MarkedExtrasFoundationProof', 'MarkedExtrasDownProof', 'HereditaryValueEqualityProof', 'HereditaryProjectionTargets', 'HereditaryEncodingTargets', 'HereditaryEncodedFitsProof', 'HereditaryProjectionLookupProof', 'HereditaryProjectionRetentionProof', 'HereditaryProjectionSemanticsProof', 'HereditaryRestrictionProof', 'MarkedExtrasRestrictionProof', 'HereditaryRestrictionAlgebraProof', 'MarkedBaseTupleRestrictionProof', 'MarkedFamilyCoherenceFoundationProof', 'MarkedFamilyCoherenceFoundationChecks']
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
 for name in re.findall(r"^'([^']+)' does not depend on any axioms",log,re.M):axioms[name]=[]
 rows.append({'module':module,'source_sha256':c.file_digest(source),'native_row':row,'outputs':c.object_bundle(target)})
 pins[str(source.relative_to(REPO))]=c.file_digest(source)
for filename in ['MARKED-FAMILY-COHERENCE-FROZEN.json','MARKED-FAMILY-CODING-FROZEN.json','MARKED-FAMILY-PARAMETERS-FROZEN.json','MARKED-BASE-TUPLES-FROZEN.json','MARKED-EXTRAS-FROZEN.json','HEREDITARY-LATTICE-FROZEN.json','HEREDITARY-ORDER-FROZEN.json','HEREDITARY-PROJECTION-FROZEN.json','HEREDITARY-ENCODING-FROZEN.json','HEREDITARY-NATURALITY-BRIDGE-FROZEN.json','HEREDITARY-DOMAIN-FROZEN.json','FINITE-DOMAIN-SCHEMA-FROZEN.json','FINITE-DOMAIN-FOUNDATION-FROZEN.json','DECISION-CLOSURE-FROZEN.json','PORT-NORMALIZATION-FROZEN.json','DECISION-SOURCE-FROZEN.json','OBSERVATION-LAMBDA-FROZEN.json','DECISION-OBSERVATIONS-FROZEN.json','DECISION-PORTS-FROZEN.json','DECISION-INVENTORY-FROZEN.json','NATIVE-ORIENTATION-FROZEN.json','GRAFTING-FROZEN.json','STABLE-PAIR-FROZEN.json','TYPE-SUPPORT-FROZEN.json','STRUCTURAL-COVERAGE-FROZEN.json','STRUCTURAL-STABILITY-FROZEN.json','FREE-VARIABLE-FROZEN.json','ORDINARY-COMPOSITION-FROZEN.json','CUT-CORE-FROZEN.json','CUT-SELECTION-FROZEN.json','CUT-OWNER-FROZEN.json','CUT-OCCURRENCES-FROZEN.json','CUT-EDGES-FROZEN.json','TARGET-EXTRAS-FROZEN.json','APPLICATION-COVARIANCE-FROZEN.json','PREFIX-ESCAPE-FROZEN.json','TWO-ENVIRONMENTS-FROZEN.json','EXTENDED-MARKING-FROZEN.json','SHARP-ADMISSIBLE-FROZEN.json','EXTRA-COMPRESSION-FROZEN.json','CONSERVATIVE-FROZEN.json','EXTENDED-RENAMING-FROZEN.json','EXTENDED-OPENING-FROZEN.json','REFINEMENT-APPEND-FROZEN.json','REFINEMENT-OPENING-FROZEN.json','REFINEMENT-RENAMING-FROZEN.json','REFINEMENT-SYNTAX-FROZEN.json','COMPARATOR-FROZEN.json','AUXILIARY-FROZEN.json','ELEMENTARY-BRIDGE-FROZEN.json','TYPED-SPINE-FROZEN.json','SUBSTITUTION-FROZEN.json','INSERTION-FROZEN.json']:
 for source,digest in json.loads((HERE/filename).read_text())['sources'].items():
  if c.file_digest(REPO/source)!=digest:errors.append('Frozen source changed: '+source)
required={'MarkedFamilyCoherenceFoundationChecks': ['exact_InputOrderExact', 'exact_DestinationValid']}
for module,names in required.items():
 for name in names:
  full='LogicLineages.PersistentMarking.'+module+'.'+name
  if full not in axioms:errors.append('Missing axiom log: '+full)
report={'status':'verified' if not errors else 'failed','local_modules':len(rows),'exact_aliases':len(axioms),'profile':profile,'errors':errors,'source_pins':pins,'axioms':axioms,'modules':rows,'context':context,'full_root_build':False,'CI':False}
(HERE/'MARKED-FAMILY-COHERENCE-FOUNDATION-EVIDENCE.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'local_modules':len(rows),'aliases':len(axioms),'errors':errors},indent=2))
raise SystemExit(bool(errors))
