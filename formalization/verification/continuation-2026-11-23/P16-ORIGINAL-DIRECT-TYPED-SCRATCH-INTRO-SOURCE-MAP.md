# Paper 16: actual typed scratch nil and cons introduction

Source freeze, pending native. This reverses only the actual one-cons
typing previously paid, not the universal pointwise statement. It supplies
two basic constructor proofs for the typed portion of the odd (A) clause
of Paper 16 `sections/ordinals.tex:84–98`, relevant to nested union 142–148.

* `exact_TypedScratchNil` uses the actual original list-map zero base and
  scratch-member zero base. The selected scratch code zero is already
  decoded nil, not a failed raw parse.
* `exact_IntroTypedScratchCons` holds a genuine original `consGraph code head tail`,
  original scalar head's exact output one, and actual selected `typedScratch i`
  output one at that tail. The already accepted exact no-zero report
  extracts the genuinely normalized mapped tail. An actual `consCode` calls
  original totality to form the mapped cons with head one and that same
  mapped tail; `InternalListMapProof.consBackward` proves this is the same
  original map's output for the original code. Since the original head
  comparison on [one,zero] is zero, the literal membership row propagates
  the same actual tail zero. The same `typedScratch i` accepts the original
  code by its actual introduction. No host testing, re-encoding or arbitrary
  membership assumption.

No object universal converse in this packet; no union, arbitrary reorder,
frequency observer, or actual J proved.

New leaves `NumberedWindowInternalDirectTypedScratchIntroTargets.lean`
SHA `ed71462dc1411866f0f52fbe184e9eafef8a453a7462683892f58d2617b6be68`
and `NumberedWindowInternalDirectTypedScratchIntroProof.lean` SHA
`919b990ccb1261474b1cbc1721a5b84eb052761bec171c2e5a360f20cebd2c8f`.
Exact gate `IntroProof.exact_TypedScratchNil` and
`IntroProof.exact_IntroTypedScratchCons`; no Hydra/GameAdd/Sym2/Linarith in
recursive source closure. Prior typed scratch report Proof (unchanged)
`f30a092f5e4dcfe2f4752be67dd48c10297b4a6933b75ca93cbec834989faf27`;
original exact list map Proof
`6891a8bc0dbb4886205a108ebf27f94271c3ca19c6916b1365b114922c73e3ed`.
