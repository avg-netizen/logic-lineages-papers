module
public import LogicLineages.OrdinalComparison.WWSourceComparisonTargets
public import LogicLineages.OrdinalComparison.WWCompiledVectorProof
public import LogicLineages.OrdinalComparison.WWEncodedComparisonProof
public import LogicLineages.OrdinalComparison.WWGroundTupleProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem scalar_field {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v = some c)
    (ρ : OrdinalComponent Γ → Nat) :
    sourceVectorAtValue v ρ 0 = (c.scalar.value ρ : Ordinal) := by
  have h := compiledVectorSound Γ n v c hc ρ 0
  simpa [sourceVectorAtValue, ordinalVectorAt, CompiledVector.value] using h.symm

private theorem positive_field {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v = some c)
    (ρ : OrdinalComponent Γ → Nat) (j : Nat) :
    positiveNoteAt c.positiveNotes j = sourceVectorAtValue v ρ (j+1) := by
  by_cases hj : j < n
  · have h := compiledVectorSound Γ n v c hc ρ (Fin.succ ⟨j, hj⟩)
    simpa [positiveNoteAt, CompiledVector.positiveNotes, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hj, sourceVectorAtValue, ordinalVectorAt,
      Nat.succ_lt_succ hj, CompiledVector.value] using h
  · have hn : n ≤ j := Nat.le_of_not_gt hj
    have hp : (c.positiveNotes).length ≤ j := by simpa [CompiledVector.positiveNotes] using hn
    rw [positiveNoteAt, List.getD_eq_default _ _ hp]
    simp [sourceVectorAtValue, ordinalVectorAt, show ¬j+1<n+1 by omega, zeroNote, denote]

theorem compiledQueryPointCorrect : Targets.CompiledQueryPointCorrect := by
  intro Γ n m a b ac bc ha hb index strict xs
  have hpoint := encodedQueryAtSourceCorrect (OrdinalComponent Γ) index strict
    ac.scalar bc.scalar ac.positiveNotes bc.positiveNotes xs
  change encodedQueryAt (compiledQueryCode index strict ac bc) xs = true ↔ _ at hpoint
  rw [hpoint]
  unfold SourceComparisonAt
  rw [scalar_field a ac ha _, scalar_field b bc hb _]
  simp only [← positive_field a ac ha _, ← positive_field b bc hb _]
  cases strict <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.cast_lt, Nat.cast_le]

theorem actualSourceQueryCompilation : Targets.ActualSourceQueryCompilation := by
  intro Γ hΓ τ υ p strict a b
  obtain ⟨av, hav, ac, hac, _⟩ := actualSourceVectorCompilation Γ hΓ τ p a
  obtain ⟨bv, hbv, bc, hbc, _⟩ := actualSourceVectorCompilation Γ hΓ υ p b
  let index : OrdinalComponent Γ → Nat := fun c => SourceTypedPorts.variableIndex c.2.1
  let q := compiledQueryCode index strict ac bc
  have hp (xs : List Nat) : encodedQueryAt q xs = true ↔
      SourceComparisonAt strict av bv (fun c => xs.getD (index c) 0 + 1) :=
    compiledQueryPointCorrect Γ τ.level υ.level av bv ac bc hac hbc index strict xs
  refine ⟨av, bv, q, hav, hbv, ?_, hp, ?_⟩
  · simp [compileSourceQuery, hav, hbv, hac, hbc, q, index]
  · constructor
    · intro h ρ hρ
      obtain ⟨xs, hlen, hx⟩ := groundPositiveTupleComplete Γ hΓ ρ hρ
      have hv := (hp xs).mp (h xs hlen)
      have he : (fun c => xs.getD (index c) 0 + 1) = ρ := funext hx
      rwa [he] at hv
    · intro h xs hlen
      apply (hp xs).mpr
      exact h _ (groundTuplePositive Γ xs)
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
