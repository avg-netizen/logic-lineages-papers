# Paper 16: the inner odd-induction motive for actual multiset union

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
lines 84–98 give J and its original strict relation, and lines 142–148 call for
nested J induction. This packet implements **only the inner induction interface**,
leaving the left code as an arbitrary open parameter.

* [Syntax](../../LogicLineages/PersistentMarking/NumberedWindowInternalCertifiedUnionInnerSyntaxProof.lean):
  the literal motive is `J(b) ∧ ∀ u (U(a,b,u) → J(u))`. The outer parameter a
  stays fixed; the current b and the quantified u occupy different variable
  slots. U is exactly the checked #1519 packed parser/append/observer formula.
* [Proof](../../LogicLineages/PersistentMarking/NumberedWindowInternalCertifiedUnionInnerInductionProof.lean):
  the lower-state accessor requires a derivation of the original strict odd
  edge and returns the inner state at that exact smaller code. A carrier
  derivation together with this lower-state hypothesis gives current J(b) by
  the original introduction rule: for every successor, project J from its
  strict lower state. This does not assume current J(b) in the odd progress
  premise. A genuine derivation of the open consequence under those local
  hypotheses then gives the checked #1517 original odd induction premise.
* The remaining progress derivation needs the genuine carrier supplier for
  union codes and the certificate-level origin split used conditionally in
  #1519. This packet does not silently add or discharge either. No outer
  induction, external Acc reflection, checker replacement, unconditional
  J-union or numbered promotion.

Native author status: source only; proof root has three named axiom audits.
