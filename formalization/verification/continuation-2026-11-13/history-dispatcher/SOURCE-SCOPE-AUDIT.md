# Source scope audit: literal history line dispatcher

Status: independent source-only audit while coordinator native/full gate runs. This note does not claim that the full gate, evidence verification, or publication has passed. No compiler/Git or mathematical source edits were performed.

## Literal checker correspondence

Definitions fixes a NEW `lineDispatcher` AST with inputs [index, fuel, history, encoded Line], not an identity theorem about the older opaque HistoryMachine kernel. Nested actual HistoryDecoder left/right projections recover the original nested product Line and Payload coordinates. NativeProof proves each selector on every original encoded Line using encode-product identities and the decoder's all-vector calibration.

The final conjunction retains actual validFormula checking. The selector handles exactly original rule0 logical, rule1 arithmetic, rule2 modus ponens, rule3 generalization, and rule4 enumerated axiom; the default branch is zero. In rules0/1, `withRule` replaces only the rule tag and preserves all original context/conclusion/payload fields. The original ruleCheck branches do not read history there, so checking them at [] is exact, not a semantic independence assumption. Rule4 preserves original axiom payload length=1, tag/reference zeros, closed-formula validity, bounded enumeration, and weakening/substitution equality via the calibrated axiomFunction.

Rule2 retains payload tag=0 AND argument list empty before invoking actual mpCheck. Rule3 retains these guards AND second reference=0 before actual generalizeCheck. NativeProof's guard identities use encode-injectivity for the empty argument list, not an assumption that payloads are canonical. Thus NativeLineDispatcher quantifies over all original Line values, including malformed formula codes, payloads and invalid rule numbers. It does not silently restrict to mpLine/generalizeLine constructors: those constructors are used only for the guarded core-call calibration and all original guards are reinstated around them.

## Leaf existence versus internal preservation

ConstructLeaves derives primitive recursiveness of the four concrete functions, including actual decode-with-default, and invokes allPrimitiveFunctions to obtain Programs with evaluation equality on EVERY vector. This is external existence/calibration; it does not supply internal graph equations for validity, logical axioms, arithmetic axioms or enumerated axioms.

InternalLineSuffix is intentionally stronger in a different direction: it works for arbitrary leaf Programs and requires NO NativeLeaves premise. The history-independent wrappers feed valid/logical/arithmetic only encoded-line projection3, and axiomProgram only projections0,1,3 (index,fuel,line). They do not pass projection2. IndependenceProof's inductive syntactic certificate admits only non-history projections and compositions whose argument Programs have that certificate. The function in such a composition can be arbitrary, including recursive, because its actual argument calls are proved identical. Its internal equality theorem uses registered defining equations and call congruence, never external evaluation reflection.

All decoder-derived selector Programs, payload guards and rule tests have explicit certificates from line projection3. PreservationProof transports exact selected branches using the literal select AST; SelectProof handles an arbitrary internal test via internal induction, not a numeral-only decision. Requiring acceptance=1 does not require all intermediate tests to be Boolean by an external premise.

## Actual rule2/rule3 addresses and suffix

BranchProof obtains functionChild at tag+1 and each argumentChild at tag+argumentTag from the literal registered composition node. The old and new argument vectors retain the SAME child addresses. The history projection equation exposes h versus the registered appendCall h tail; context/raw/reference selector calls are related using their syntactic independence at those exact child nodes. A mixed argument vector then applies the already internal mp/generalize suffix theorem at that actual functionChild, followed by call congruence back to the new vector.

No cross-copy decoder, lookup, or checker address is identified by fiat. No successful-reference, coded-list, line-validity, or native-leaf premise is added to InternalLineSuffix. Its terms index/fuel/h/tail/line are arbitrary object-language terms. The sole operational assumption inside the implication is original dispatcher acceptance=1; outer assumptions identify the real dispatcher and append nodes in one ambient registered Program.

## Boundary

This proves acceptance preservation under appending an arbitrary encoded-history tail at the literal line dispatcher. It is not a complete state transition/iterator theorem, arbitrary raw/default-state native calibration, an identification with the old opaque HistoryMachine kernel, a proof-list composition theorem, or HB2/HB3 for the selected presentation. ConstructLeaves and NativeLineDispatcher must remain distinguished from InternalLineSuffix. No concrete scope defect or circularity was found in the inspected source route.

## Reviewed source hashes

```text
22f1ce3a5583080956fe5b0bdc076f2f3789cc99534fff864d79e35db99b9d64  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/BranchProof.lean
e965a7e97172e4a65b23eaa684c1d8fd44af921cb5a7225decca16b14e89b92a  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/Definitions.lean
80fc6a1d7372c5a361dc0581ed183530875631bbe15e86b8173620b2540d61f3  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/IndependenceProof.lean
86e388401a328bb93bc7dedf42b308c2385f9c68f244da17ebdea2eebc29f281  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/LeavesProof.lean
0cac0ad0aa87f7f53705de72c260670c761f3d2352c54e243b3134676cbcaad2  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/LeavesStatementChecks.lean
cf6251a5d8d2155d69dc2819bb74e2464ecaf07d2906ee3b3a2c642a946befc6  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/NativeProof.lean
de5251383dd7557bf5c1e04e95e36ead7d7d001a3c5880ed80a6af7ce7704245  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/NativeStatementChecks.lean
bd8158f2cc32cc773779c56f39b2283faea0cf5f26593b521dd22aaedbbb8a2f  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/Preflight.lean
56356597b69ea6b958ce143aa26d58e468498cbb2618b434f77f67ec3d334f73  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/PreservationProof.lean
ef5e77510d4033ec2cc43c1fe47a4ca46fdf3fd31903da53587ee00d8c4f165a  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/SelectProof.lean
00240b3195e8bdc3fb037bf0f1429f34bc5a6c08f4affe9447321b0af5b08a0b  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/StatementChecks.lean
bc9786f626b25be0c30b963eec26161ce8653c4b0bc16737248e69f6918e05c5  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/SuffixProof.lean
2f40a1c47eb527dd6486bc83f169d7c42b86e4052ad22657f5e88cff92e82277  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDispatcher/Targets.lean
edab7ab6c256d8cb7e7b0f61c5ec55a7cf262b798c52566f4807dcc651071b9e  LogicLineages/ComputabilityKnowledge/GorbowProofChecker.lean
d3816e1871d7e4f49e8530af66c2d3ddac749cebfe9aa1461aba4bdca0eed7c9  LogicLineages/ComputabilityKnowledge/GorbowTheoryChecker.lean
```
