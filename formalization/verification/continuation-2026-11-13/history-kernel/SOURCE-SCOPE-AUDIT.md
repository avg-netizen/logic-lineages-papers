# Source scope audit: literal history kernel

Independent source-only review. Coordinator reports exact5 PASS `1794574921998893396-18` and source-matched evidence of 481 modules, zero errors. This worker did not run Lean/Git or independently verify publication.

## Actual codec and native scope

StateCodecTotal is proved for the original `Option History × List Line` codec, not postulated. CodecTotalProof builds surjectivity from Nat, actual product pairing/unpairing, successor option encoding and successor-pair list encoding. List totality uses external Nat strong induction with the actual unpaired tail strictly below the successor input. The original nested Line/Payload structure is retained. `encodeDecoded` follows from this surjectivity plus the original encode/decode law; no raw-code subset is discarded.

NativeProof first proves the literal AST agrees with the original transition on every original State: empty lines stutter, NONE stays NONE while a line is consumed, SOME history appends the actual current (context,conclusion) entry only on lineCheck acceptance. The accepted line uses the calibrated original whole dispatcher, including all malformed payload behavior. It then applies that theorem to `decodedState v.head` and uses `encodeDecoded` to obtain equality to the original kernelFunction on ALL vectors. Thus default decoding is accounted for by proved actual codec totality, not silently erased. NativeLeaves is an external all-vector premise here and is independently constructible by the dispatcher packet.

## Internal installed guard and successful-step closure

The kernel AST deliberately tests `equalCode checkedLine 1`, rather than treating every positive arbitrary leaf output as acceptance. The internal suffix theorem has arbitrary leaf Programs, without NativeLeaves or Boolean-range assumptions. KernelNodes derives the actual equality-test, selector, dispatcher, output pair and output cons child addresses from the registered literal kernel node.

EqualProof proves actual equalCode soundness through the installed two-difference test and internal double-zero comparison, and completeness through diagonal difference equations and congruence. OptionProof obtains the equality test's internally proved zero-or-one range; successful option output therefore implies dispatcher output EXACTLY one. It never assumes the dispatcher/leaf output range externally.

NormalProof exposes the actual kernel equation on the explicit activeState pair(SOME h,cons line rest). SuccessProof uses the actual output-pair copy congruence and pair injectivity to recover the option equality. The zero option branch contradicts SOME out, and successor injectivity recovers both dispatcher acceptance and out=the actual new cons history. No successful line, reference bounds, or output-history reconstruction is supplied as a premise.

SuffixProof feeds the recovered acceptance into the genuine dispatcher suffix theorem, reconstructs the accepted new option, and uses the original internal append-cons law at its installed cons address to identify the new history with append(out,tail). Explicit pair-copy congruence returns the exact caller-selected output pair. All source terms index/fuel/h/tail/line/rest/out remain arbitrary internal terms. The only logical antecedent is the old actual kernel step returning pair(SOME out,rest).

## Limits

InternalStepSuffix is for explicit successful active states; it does not state unrestricted arbitrary-state internal suffix equivalence or rejection preservation. Native all-vector calibration is separate. This is a NEW literal kernel with the old kernelFunction, not an AST identity with the earlier opaque existential kernel, nor a proof that all selected historical tuples use it. Whole-run/proof composition and selected-presentation HB2/HB3 remain separate obligations. No concrete circularity or scope defect was found.

## Reviewed snapshot

```text
5ab2c5676001690fc6bdf92e54de5ae0a40ec33538bd583a6de74de2559d95eb  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/CodecStatementChecks.lean
54dc550a0aa02ce3a18400df1cf3349ab0488436c7cb782e13a5967a4870aa2d  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/CodecTotalProof.lean
5521ac1f76b622b977dc560cfa12841deb4b52e921611397f71e938ab86babe5  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/Definitions.lean
4bd406789e46c666c3623e1c21482ce582664ad76486097706f6a540d6f2a873  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/EntryProof.lean
91a3eb9f94fa19fa7c5fc4c7cd2bd4ee5cdba71e0914a1f0b6128af2ed605959  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/EqualEquationsProof.lean
112388db647f45e0beafbfb01ba624d4045022c5b2ba10a19c4cc21626e8d676  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/EqualProof.lean
f98f28a830b937b98952564e3e837af704b4e69d37e66b264d251e0b1f29dd21  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/EqualityStatementChecks.lean
91df1bc576a6b6dd93ca03c2a0d4dfd7c8f4cb4d36cd0e3bb613ac20dc8d8552  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/FieldsProof.lean
5cbb099f653b786b461bd6d344499f887722467f36cd9e495615a4a136dde100  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/NativeProof.lean
4e91bf73ad3215faed12bd86fffbd0ed295eba57b7a4f4b757753004e90db8c9  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/NativeStatementChecks.lean
a42867766a4405d3f8c6fc4a988d55ce6677e488d21c13aefd9c6207151c5f18  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/NormalProof.lean
8315dbae402ced9ae3fab917242c2a461b9e565a4544d13ed5b3e97542e28706  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/OptionProof.lean
4b85494f30dc5247838fa40697e4f8b5729a682a4fc3bc93b99a4bfce72078a6  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/Preflight.lean
4ac5716703315f0a3b7bfba095e8c9b425b6065b62d702f89ef867eb4fc72554  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/RangeProof.lean
c964a51f7897b160a15bcb680ceb135422935694439d3a9d5ebe4f572a7d2480  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/StatementChecks.lean
7684d172393b228be9a2b760e207dc345c06e95303265d0397de115f399c41b9  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/SuccessProof.lean
c2120ae0437e90a22df4347df778af22aedbd6b5b374f1843781e6089f04bd0b  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/SuffixProof.lean
78fbc215005b7d8f995de6a1e47a9a1cacb7f33857ae0db7bcb1b709104f5205  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/Targets.lean
2dda87c2ce08d3613d1cef534f7be961be22a73cb9cc94132125046e6368659d  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryKernel/TransitionEquationsProof.lean
```
