module
public import LogicLineages.OrdinalComparison.WWOriginalAtomicAssignmentTargets
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem one_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) :
    actualOrdinalNorm (expressionValue ρ .one) = 1 := by
  simpa [expressionValue, denote] using (finiteNorm 1).2

private theorem omega_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) :
    actualOrdinalNorm (expressionValue ρ .omega) = 2 := by
  simpa only [expressionValue, denote, Nat.cast_one, mul_one, Nat.cast_zero,
    add_zero, Nat.mul_one, Nat.add_zero] using actualFiniteHeadNorm 1 0

private theorem expand_ambient {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, AmbientGrade Γ i (xs j)) :
    AmbientGrade Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

theorem originalVariableAssignmentBounded : Targets.OriginalVariableAssignmentBounded := by
  intro Γ τ p x
  refine ⟨fun j => .var ⟨τ, x, j⟩, rfl, fun j => .var x j, ?_⟩
  apply (originalBoundedVectorSupportBridge Γ _ _).mp
  intro ρ j
  exact ρ.bounded x j

theorem originalOneVectorBounded : Targets.OriginalOneVectorBounded := by
  intro Γ m
  refine ⟨fun j => .one j.val, (originalBoundedVectorSupportBridge Γ m _).mp ?_⟩
  intro ρ j
  exact le_rfl

theorem originalRecursorAssignmentBounded : Targets.OriginalRecursorAssignmentBounded := by
  intro Γ σ p
  let v : OrdinalVector Γ σ.recType.level := fun j =>
    if j.val = 0 then numeral p 2 else if j.val = σ.level + 2 then .omega else .one
  refine ⟨v, rfl, ?_, (originalBoundedVectorSupportBridge Γ _ v).mp ?_⟩
  · intro j
    dsimp only [v]
    split
    · exact expand_ambient (p.shape .numeral 1) (fun _ => .one) (fun _ => .one j.val)
    · split
      · rename_i hz he
        exact .omega j.val (by omega)
      · exact .one j.val
  · intro ρ j
    have hn : actualOrdinalNorm (expressionValue ρ (numeral p 2)) = 2 := by
      rw [numeral, originalPositiveRepeatNorm Γ ρ p .numeral 2 .one (by decide), one_norm]
    have h0 : v 0 = numeral p 2 := by simp [v]
    rw [h0, hn]
    dsimp only [v]
    split
    · exact hn.le
    · split
      · rw [omega_norm]
      · rw [one_norm]; decide

end LogicLineages.OrdinalComparison.Source.OriginalDomain
