# AST-only relocation assessment (read-only source analysis)

Status: legitimate in principle; no new implementation approved or native equivalence claimed. Original frozen contract remains unreleased by this assessment. No compiler run.

`OriginalCandidates` executable declarations are `filterStep`, `filterCandidates`, `candidates`. Their dependency on `OriginalClassCodes` is the actual guarded `classCodes` plus `gamma`. ClassCodes executable cone must retain seed rejection, exact size/fuel, head encoding map, enumeration input nesting, root pairing and list order. Its `classCodesValue` is a numeric specification, not required to construct this AST; omission must be explicit, not silently treated as checked correspondence.

OriginalEnumerationMembership.Definitions adds no executable AST, so its imported proof suite is not intrinsically required to construct ClassCodes. However removing only that import does not suffice. Static import traversal still finds:

OriginalEnumerationRecursion.Definitions -> OriginalEnumerationRecursionInterface.StatementChecks -> NativeCombineProof -> OriginalEnumerationConstructorLayer.NativeProof -> NativeHeadsProof -> NativeBranchesProof -> NativeSupportProof -> OriginalEncodedNumberedEnumerationBranch.NativeProof -> NativeSupportProof -> Targets -> Definitions -> OriginalNumberedEnumerationBranch.CrossIntroProof -> CrossIntroCoreProof -> CrossIntroBindingProof -> CrossIntroInductionSyntaxProof.

The original BoundsRecursion, DecodedContextValidity, SourceHeads and HeadEncodingBridge Definitions have no path to that particular blocker in current static traversal. This is not a native resource or success prediction.

## Required new packet

* New namespaces and fresh comparator explicitly naming relocated constants, never shadowing old names or substituting arbitrary Q.
* Full executable dependency cone inventory, identifying unchanged providers and each relocated declaration.
* For each selected declaration: original and destination paths, whole-file SHA256, exact selected text/spans and SHA256; machine comparison after only an explicit qualified-name mapping. No arithmetic, defaults, annotations carrying semantics, branch order, recursion/fuel, input vector order, or binder/premise changes.
* Explicit list and justification of omitted specification/proof/unused declarations; import replacements and resulting static closure report, including absence of blocked modules.
* Literal expanded target gate and comparison of quantifiers/premises/conclusion against old frozen target except mapped constants. Keep all old sources/frozen/evidence untouched.
* Independent source review, fresh frozen pins, native gates and recursive source-matched evidence. Source text comparison is not a native theorem equating old/new constants and must not be described as release of the original frozen contract.

A generic filter/list closure helper may be a useful independently proved preliminary lemma, but cannot itself replace exact Candidates in the endpoint or count as completion. No presently verified alternate route releases the exact old target under fixed caps; any original-namespace exact theorem still imports the old closure unless the existing unchanged gate eventually passes. Do not change limits or acceptance evidence.
