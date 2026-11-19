# Paper19 lem:chain: one actual final abstraction under the selected policy

Current numbered source: paper19 `sections/realization.tex` 131–144, with
the common-unit convention in lines 1–20 and the fixed selected policy and
permitted control in the setting. Every supplied V is an actual unary source
in the same original context Γ, independent of the fresh ground x. The
existing `SourceUnaryChain.chainBody`/ `chainSource` are the literal
right-nested applications and exactly one final lambda. Their use is
syntactic only; the historical checked theorem uses the default policy
and does not satisfy this current theorem.

* Freshness is the real typed `Term.rename (Renaming.weaken Γ ground)`,
  including existing nested binders. No fresh source scalar is assumed
  and no operator scalar is replaced by one. Source may have arbitrary
  internally typed constructors and free names with ambient Γ. The
  current lemma allows empty list (head one) and arbitrary list length.
* The literal `scalarSpine` retains each operator's complete actual
  ordinal assignment, both positive head and scalar, and applies the
  exact ground-argument canonical box. `ActualBody` requires actual
  selected-policy assignment of this exact source body.
* The literal `partialSpine p` follows the actual structural
  `AdmissiblePartial.run p` at 0: free head's positive partial contributes
  head + 1, and the actual policy-selected three operand active add
  contributes 1 + inherited partial + 1. The scalar partial uses the
  same genuine collapse/active-add tree, retaining actual operator
  scalar. `ActualPartial` binds this to the existing actual partial,
  rather than treating the displayed calculation as an assumed theorem.
* `HeadValue` records aligned actual term assignments p and an actual
  one-lambda result assignment, with `denoteWith f` on the real first
  coordinate and the recursive Hessenberg natural sum of the operator
  first fields plus 3, ending at 1. Both p and f remain arbitrary; the
  algebra works at any f/valuation and hence covers the manuscript's
  permitted/current control as stated, without transferring a fixed
  gamma/Phi/default theorem. Only a single already-evaluated ordered
  sum is insensitive to the policy's association; never reassociate a
  source expression before taking a partial.
* `CommonUnitValue` explicitly names the statement's observation:
  keep genuine shared ground inputs (positive raw coordinates from
  standard Nat wire plus one), and put ordinal one in each coordinate
  of every remaining functional name. This is a valuation, not an
  assertion of an actual all-one lambda term. The exact same list
  assignments and context are used.

No representability, algorithmic bound, end-to-end ground-construction, or
closed all-one inhabitant is implicitly claimed by this lemma. No existing
historical or accepted source is modified. Freeze these two new modules
and source comparator before proof, take independent scope review then
target-only preflight under the original profile, and use separate
authored/final/recursive evidence gates before acceptance.
