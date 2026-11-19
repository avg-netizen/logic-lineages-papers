# Paper16 least Nat code of the actual primary class

Source: ordinals.tex lines 13–29 (one fixed declaration-retaining typed
window and all actual finite contexts), and 69–76 (literal primary
congruence, finite effectively enumerable classes, least-code
representatives permitted). This packet computes the actual least
literal Nat code, not an arbitrary equivalent term chosen thereafter.

- **Actual finite list and code, no oracle.** Map packet450's exact
  original NTerm constructor codec over packet447's exact finite class
  list, then use literal List.min? in the Nat order. Duplicates in the
  class list do not affect leastness. Decode that *same computed code*
  with packet450's actual term decoder. No assumed least solution or
  interpreter postulate. No type/label/argument pruning.
- **Actual class and leastness specification.** Starting with just the
  actual admitted source Q in the subtype-closed K, prove that the
  result is some code/actual NTerm, with that exact encoded value,
  in the same real window/context/type and actual original Primary
  class. It is no larger than the true numeric code of every actual
  Primary-equivalent term, with no target-side added guard, and any
  actual equivalent having the same code is literally that output.
- **Class invariance on actual admitted representatives.** The equality
  tests are stated only on two original admitted terms in the same
  type/context/window, i.e. the actual class carrier; both source guards
  are visible for evaluating the two algorithms. Least-code equality
  and decoded-representative equality each reflect exactly original
  Primary, via original symmetry/transitivity and the actual injective
  term codec, not mere erased head-rank equality.
- **Same actual quotient.** The quotient target uses the existing
  NumberedWindowSimulationData.WindowCarrier, Class, and classOf,
  unchanged. Proof must identify classOf equality with that actual
  Primary using its known equivalence laws and genuine Quot
  exactness/soundness; it must not introduce another quotient or
  a new membership predicate defined by code equality.
- **Finite context scope and limit.** Every endpoint is explicitly
  over original nearest-first prefix Γ EmptyContext. No arbitrary
  function C is coded. This is least numeric class representation
  only, not a numeric typed/RawStep/RS certificate graph, a formal
  arithmetic formula/program translation, PA/ID1 accessibility, or
  an ordinal rank equality. Source and accepted dependencies unchanged.
