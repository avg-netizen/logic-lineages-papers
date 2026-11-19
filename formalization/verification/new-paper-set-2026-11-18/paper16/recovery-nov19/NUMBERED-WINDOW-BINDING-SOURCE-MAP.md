# Numerical binding suppliers, source-first only

These five supporting propositions do not assert any numbered endpoint.
They are frozen separately before proofs, in
`NUMBERED-WINDOW-BINDING-FROZEN.json`, and use the exact numerical syntax
already preflighted for `lem:tuple-simulation`. No additional context,
finiteness, numeric marker, or old Paper06 proof is assumed.

- `SingleCancellation` and its Args variant remove exactly one anonymous
  binder inserted by the actual `shift`/application body. The statement
  is cutoff-general for induction through residual lambdas, and is a
  raw equality, so it also specializes to the literal root at cutoff zero.
- `SinglePushBlock` and its Args variant compare actual singleton numerical
  beta after an outside finite substitution with the actual nearest-binder-
  first combined block used by `Spine.applyAux`. Type validity is separate;
  the raw equality imposes no extra target premise. This equality tracks
  the original unmodified lambda spine, not a re-evaluation of a substituted
  functional image as a new source head.
- `OpenNumberedBeta` is the literal result of the actual numeric opening
  body after beta. Old shifted base/extra terms recover precisely by
  cancellation, then its fresh bound 0 is the actual supplied numeric
  argument. Lists retain original order and old extras remain first.
  The label is the already-decremented label of that body; the raw FAbs
  edge separately pays the genuine leading decrement.

Useful in-family proof patterns are `FreeShiftProof.cancellation` and
`BoundBlockProof.block` on the actual original symbolic syntax. Neither
kernel theorem transposes automatically: the raw numeral proof includes
new typed application, bottom and numbered heads with numeric labels.
Likely ordering: zero shift and args append/get arithmetic; cutoff
cancellation; singleton block decomposition into the three bound-index
ranges (below, inside, after); literal open/beta. Core Lean only. A complete
normalized typed full application path and whole source tuple remain
separate.
