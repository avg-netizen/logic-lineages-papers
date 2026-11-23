# Paper 16: repeated literal native cap block-path witnesses

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
499–511 defines the actual typed (Z), (s), (\mathrm{Cap}(P,U)) and
(\omega)-carrier (\mathrm{Cap}(s,Z)). The new family only iterates that
literal cap constructor with the same native (s).
This is a rank-free supporting witness, not the statement about exact
descending height at 634–636 and not the original Bachmann–Howard tower.

* [Targets](../../LogicLineages/PersistentMarking/NativeOrdinalRepeatedCapBlockTargets.lean):
  for any genuine closed index-type payload (u), take (C_0=u),
  (C_{k+1}=\mathrm{Cap}(s,C_k)), and take the original finite application
  (s^m(C_k)) as block occurrence ((k,m)).
* [Proof](../../LogicLineages/PersistentMarking/NativeOrdinalRepeatedCapBlockProof.lean):
  exact native finite-application fusion reuses #1511's original two strict
  steps through each successor instance for a witnessed (2(d+1))-link
  path from ((k,m+d+1)) to ((k,m)). From any freshly selected
  ((k+d+1,n)) to any original earlier ((k,m)), first peel its own
  successor applications ((2n) links), then use the actual cap over the
  preceding base (d) times, then use the actual cap edge over this exact
  earlier selected occurrence. This witnesses (2n+(d+1)) links.
* The special base (u=Z) starts at the same original (Z) and has the
  very same original native omega carrier at cap stage one. All intermediates
  remain at the same actual (o\to o) type in the same signature.
  The relation is `NativeBelow`, not claimed to consist only of beta
  reductions, and lengths are neither shortest nor maximal. No ordinal
  interpretation, transitivity or rank lemma is imported or inferred.

Native author status: source only; three named axiom audits.
