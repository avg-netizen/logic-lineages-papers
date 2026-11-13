# History decoder: independent source-scope audit

Coordinator reports calibration exact4 PASS1794564849102416672-6; native source-matched evidence is running. This audit is read-only source analysis, with no compiler/Git or accepted-source edits. No concrete AST, registry-address, or scope defect found.

## Exactly what the checked four contracts establish

CalibrationStatementChecks exports NativeLeft, NativeRight, LeftPairInstalled and RightPairInstalled. The first two prove for EVERY one-element natural-number input vector that evaluate(decoder false/true) returns the corresponding component of Nat.unpair. This is an all-vector metatheoretic calibration, not a few examples and not an internal arithmetic derivation. The other two prove registry-node identities for the actual pair copy inside each installed decoder.

Targets.InternalLeftInverse and InternalRightInverse are separately frozen specifications. They require INTERNAL Derivation of decoder(pair(a,b)) = a/b for arbitrary internal terms at the actual installed pairTag. They are NOT among these four checked aliases and remain unpaid by this packet. Native calibration must not be reflected into those statements.

## Literal bounded-search AST

Definitions uses explicit Program recursion/composition/projection nodes, not an opaque primitive-recursive existence witness. Candidate is the literal HistoryCodec.pair on [a,b]. The inner step sees [b,previous,a,code,seed]. Both original truncated differences code-pair(a,b) and pair(a,b)-code must vanish before the coordinate replaces previous; otherwise previous is preserved. False selects a and true selects b.

The inner recurrence scans b=0 through countB-1, seeded by the prior outer result. The outer recurrence scans a=0 through countA-1 and gives every inner scan code+1 iterations. The final decoder supplies countA=code+1 as well, hence both coordinates are scanned inclusively through code. NativeProof calibrates each of these literal recurrences, proves finding and preservation, and applies the ordinary Nat.pair preimage bounds and Nat.pair_unpair. Use of Nat.pair injectivity in this NATIVE proof is appropriate; it is not a proof of the internal inverse specs.

## Exact installed pair address

InstalledProof follows the actual AST child chain:
 decoder composition function -> outer recursion step -> outerStep composition function -> inner recursion step -> innerStep argument zero (forward) -> forward argument zero (candidate) -> candidate composition function (pair).

Each hop uses the existing registry functionChild/recursionStepChild/argumentChild theorem. The sum in pairTag is precisely this chain's actual offsets, ending at a node of arity two with the literal HistoryCodec.pair AST. No arbitrary pairing symbol or merely extensionally equal substitute is installed. Other pair copies in the AST need their own identities/congruence when used internally.

## Pair-copy congruence boundary

PairCongruenceProof.pairCopies constructs internal equality between TWO installed literal pair copies on the SAME arbitrary terms a/b. It splits internally into lower/upper sectors, rewrites both calls with their actual registered branch equations, and discharges the sector hypotheses. It does not appeal to native decoder calibration, native Nat.pair equality, a standard model, or an assumed inverse.

This is useful cross-copy symbolic congruence, not decoder correctness. CalibrationStatementChecks does not import PairCongruenceProof, so the reported four-contract gate alone does not establish that separate module's acceptance. This review inspects its source route without inventing a native receipt for it.

Remaining work: actual internal bounded-scan invariants and inverse proofs, then list decoding/history lookup and subsequent proof-history infrastructure. The present result must not be advertised as completed internal decoding or HB2/HB3.

## Reviewed hashes

- `Definitions.lean`: `e21acd8a4bc7ebe59fb066f4e129730f7126628a00cab9effafadea1b1d72ebe`
- `Targets.lean`: `bc3d858fd978d372ff8ac5cd88f744f6e3f75dc128816ce817906dd423ce691b`
- `NativeProof.lean`: `4de007f448c1f9b427469a9c1c311f615aae760d78a2eb2a6b172a3cb1021922`
- `InstalledProof.lean`: `c36c30ddc008c9c097fddf95b7ebe3185e23da7077f7d20e507b795aa46b01cf`
- `CalibrationStatementChecks.lean`: `6801ade7535779f2670a9f1c446807fb8b6cde61c368c04c320999f7828f919a`
- `PairCongruenceProof.lean`: `49ab949d6b6940002eceec73c57ba4ff94d813f0d1c36dfceee7bf663772238a`


# Follow-up: internal inverse source route

This section supersedes the earlier unpaid-inverse source status, but NOT its native verification status: at this assignment the full six-target `StatementChecks` gate is underway, not reported passed. The four-target calibration receipt does not alone certify these new inverse modules. No compiler/Git was run in this review.

The new `InverseProof.internalLeftInverse` and `internalRightInverse` match the frozen targets: arbitrary registered enclosing Program p, an actual installed literal decoder node, arbitrary context and internal terms a,b; conclusion in `GorbowPRNumeralCalculation.Theory p` that decoder applied to its own registered pair child returns the chosen coordinate. There is no model-valued premise, native calibration reflection, decoder oracle, supplied loop invariant, or additional bound premise.

The source route is internal throughout. `StepGraphProof` derives the disjunction that a literal step preserves the accumulator or both differences vanish and the actual candidate pair matches the code. `StepInvariantProof.stepHit` derives a hit using diagonal difference laws. `stepPreserve` uses checked internal pair injectivity to show any genuine later hit has the same chosen coordinate. Registered copies are reconciled by the pair-congruence/step-normal route, not silently identified as function symbols.

`InnerPreserveProof` performs PA induction on arbitrary scan count with the correct coordinate as initial accumulator. `InnerFindProof` performs PA suffix induction on count v + (k+1), starting at the exact candidate b=v from an arbitrary seed. `InnerCompleteProof` uses the internal pairSecondBound existential (code = v + offset) to cover the literal inclusive count code+1; it eliminates the offset internally. `OuterFindProof` similarly finds row a=u, using innerComplete, and preserves it through later rows using innerPreserve. `InverseProof.outerComplete` pays outer coverage using the actual pairFirstBound and internal existential elimination. Thus neither coordinate coverage is assumed or inferred solely from native arithmetic.

`OuterEquationsProof` extracts the actual recursion/composition children of the registered AST and proves the successor equations and decoder equation at count code+1. Its pair address agrees with frozen pairTag through decoder function, outer recursion step/function, inner recursion step, forward argument and candidate function child. Final inverse is scoped to this actual pair child. Application to another separately registered codec requires an explicit copy-congruence argument; it is not automatically a theorem about any numeral-tagged pair symbol.

No concrete scope defect found. These two internal inverses, if the full native gate passes, add genuine internal decoder correctness beyond calibration. They still do not establish history lookup, append/history laws, or Hilbert–Bernays conditions. The historical calibration-only unpaid status should not be retained as a claim about these new source proofs, nor should a full pass be claimed before its receipt.

## Follow-up snapshot

```text
6801ade7535779f2670a9f1c446807fb8b6cde61c368c04c320999f7828f919a  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/CalibrationStatementChecks.lean
22b71cbdb04497a59675af4453d27c5f47751988559c11a2d47ed30eeefd9407  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/ComparisonProof.lean
e21acd8a4bc7ebe59fb066f4e129730f7126628a00cab9effafadea1b1d72ebe  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/Definitions.lean
62916f31cdd9db087b8d2bc8d6be457f6ad638428bb834951c961a6fab3eea37  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/InnerCompleteProof.lean
3502994e18427400322affbb67b4544d3040cf6ca3ffa5a5a6f17f30d439bc2f  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/InnerEquationsProof.lean
4444446d804344586cdfd4a21fbf818c3a55a78d7049460f76fb9e7ed49ccdce  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/InnerFindProof.lean
946c209ede9d3dbe9364f306c80bf6174b3fab957467b7482d1bd3f794df4af7  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/InnerPreserveProof.lean
c36c30ddc008c9c097fddf95b7ebe3185e23da7077f7d20e507b795aa46b01cf  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/InstalledProof.lean
4d8cbaef0370b9fcd4080d4c5597304881f936eff1d949a4f20edf81efb7f91d  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/InverseProof.lean
4de007f448c1f9b427469a9c1c311f615aae760d78a2eb2a6b172a3cb1021922  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/NativeProof.lean
c4363bbb5d0810dc705d1b05810313fc0bc296c03b41039679d102725f1a0e7a  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/OuterEquationsProof.lean
d1eb67fcee9fe097cd10dbd94f3793b9e65be86d06a3004525bcf75c88a8b7af  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/OuterFindProof.lean
49ab949d6b6940002eceec73c57ba4ff94d813f0d1c36dfceee7bf663772238a  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/PairCongruenceProof.lean
9d17559dd077c5faedbc39e9fdabb358359f0424c43d381df6e427ee0d255a45  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/Preflight.lean
789ceb0a2668dd819dd3de07674e2a06ddeaea625aaa10052919db553eece9c1  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/SelectGraphProof.lean
03d47f872a513d7fd52cd45fe6556a4e7ee7760954bb8175d2548fb9624b6625  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/StatementChecks.lean
f4590d96cf773b56cc2e698d8281222e7f03a4cace5ccb848be5dc8162a145f0  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/StepEquationsProof.lean
0af3c328985c0b1da20daf0f29353213beab9a99e90ad2c50e3ad1baf79d8169  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/StepGraphProof.lean
15fa7d4034b80cd987f0d188c614d4c43e371ac9843036fe0415a023e9a6e03c  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/StepInvariantProof.lean
e3592e3f212a21009f9534543dbe2abdde31f156273d2d9308f8abe9808cd84b  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/StepNormalProof.lean
bc3d858fd978d372ff8ac5cd88f744f6e3f75dc128816ce817906dd423ce691b  LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryDecoder/Targets.lean
```

Coordinator update: full exact6 gate PASS1794565595243459565-6; native evidence verified405 source-matched modules, zero errors. Internal inverse review bytes unchanged.
