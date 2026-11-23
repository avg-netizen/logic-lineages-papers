# Paper 16: open progressive induction on the actual odd multiset tag

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex),
lines 84–98 define the one tagged source body with the original strict certificate relation.
Lines 142–153 use outer and inner inductions on that same odd slice.
This leaf provides **one** reusable syntactic induction invocation in its opened
form; it does not supply the nested progress derivations.

[New exact root](../../LogicLineages/PersistentMarking/NumberedWindowInternalOddProgressiveInductionProof.lean):
* `oddLower` is the original odd `edge data true c` from the current term to
  a fresh bound term. The current term remains in the old context and the new
  bound term replaces only the distinguished argument of the arbitrary invariant.
* `exact_OriginalOddLowerInstance` uses actual object-calculus universal and
  implication elimination. An open original edge proof is required and all old
  invariant parameters are preserved by the indicated simultaneous substitution.
* `exact_ActualOriginalOddProgressiveInduction` takes a genuine object-calculus
  progress derivation under the actual typed carrier and strict-successor
  invariant. Checked `sliceReplacement` gives those hypotheses from the actual
  selected replacement body; checked `actualInternalSliceInduction` discharges
  progression on the **same** original tagged source and concludes the invariant
  under `J(t)`. The nonselected scalar slice is left unchanged by that rule.
* No new equation for J, no external list/Acc induction substituted for object
  derivation, no installed count oracle, no certificate-level origin split
  or reconstructed certificate, and no J-union or numbered result are claimed.

Native author status: source only; root will check the two named axioms.
