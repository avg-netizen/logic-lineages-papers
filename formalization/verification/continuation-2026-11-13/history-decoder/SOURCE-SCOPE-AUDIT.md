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
