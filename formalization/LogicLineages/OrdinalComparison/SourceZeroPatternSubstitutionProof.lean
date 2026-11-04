module
public import LogicLineages.OrdinalComparison.SourceZeroPatternSubstitutionTargets
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceZeroPatternSubstitution.Proof

theorem lookup_image {n m : Nat} (r : Fin m → Fin n) (hr : Function.Injective r)
    (j : Fin m) : lookup r (r j) = some j := by
  classical
  have h : ∃ k, r k = r j := ⟨j, rfl⟩
  have he : Classical.choose h = j := hr (Classical.choose_spec h)
  simp only [lookup, dif_pos h, he]

theorem lookup_none_iff {n m : Nat} (r : Fin m → Fin n) (i : Fin n) :
    lookup r i = none ↔ i ∉ Set.range r := by
  classical
  change lookup r i = none ↔ ¬ ∃ j, r j = i
  unfold lookup
  split_ifs <;> simp_all

theorem exactIndices : Targets.ExactIndices := by
  intro n m r hr
  refine ⟨lookup_image r hr, lookup_none_iff r, ?_⟩
  intro A inst x
  constructor
  · intro j
    simp only [extend, lookup_image r hr j]
  · intro i hi
    simp only [extend, (lookup_none_iff r i).mpr hi]

theorem ordinalMeaningTransport : Targets.OrdinalMeaningTransport := by
  intro n m r x d hr
  have hz : SignedPair.signedCNF (0 : Ordinal) = 0 := by
    simpa using SignedPair.Proof.cnf_nat 0
  induction d with
  | unit => rfl
  | var i =>
      cases h : lookup r i with
      | none => simp [substitute, h, extend, zeroExpression, SignedPair.meaning, hz]
      | some j => simp only [substitute, h, SignedPair.meaning, extend]
  | add a b iha ihb => simp only [substitute, SignedPair.meaning, iha, ihb]
  | neg a ih => simp only [substitute, SignedPair.meaning, ih]
  | shift a ih => simp only [substitute, SignedPair.meaning, ih]

theorem polynomialMeaningTransport : Targets.PolynomialMeaningTransport := by
  intro n m r x d hr
  induction d with
  | unit => rfl
  | var i =>
      cases h : lookup r i with
      | none =>
          simp [substitute, h, extend, zeroExpression, SourceFiniteExponentProjection.polynomialMeaning]
      | some j => simp only [substitute, h, SourceFiniteExponentProjection.polynomialMeaning, extend]
  | add a b iha ihb =>
      simp only [substitute, SourceFiniteExponentProjection.polynomialMeaning, iha, ihb]
  | neg a ih => simp only [substitute, SourceFiniteExponentProjection.polynomialMeaning, ih]
  | shift a ih => simp only [substitute, SourceFiniteExponentProjection.polynomialMeaning, ih]

end LogicLineages.OrdinalComparison.Source.SourceZeroPatternSubstitution.Proof
