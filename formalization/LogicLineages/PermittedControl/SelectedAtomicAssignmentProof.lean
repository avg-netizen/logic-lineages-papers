module
public import LogicLineages.PermittedControl.SelectedAbstractionBoundedProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedAtomicAssignmentProof
open OrdinalComparison Source SelectedSourceDomain SelectedBoundedDelta
open Source.AdmissibleSum Source.AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem one_norm (ctrl : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ) :
    actualOrdinalNorm (expressionValue ctrl ρ .one) = 1 := by
  simpa [expressionValue, ParametricSourceSuccessor.denoteWith] using (finiteNorm 1).2

private theorem omega_norm (ctrl : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ) :
    actualOrdinalNorm (expressionValue ctrl ρ .omega) = 2 := by
  simpa only [expressionValue, ParametricSourceSuccessor.denoteWith, Nat.cast_one, mul_one, Nat.cast_zero,
    add_zero, Nat.mul_one, Nat.add_zero] using actualFiniteHeadNorm 1 0

private theorem expand_ambient (ctrl : Nat → Nat) {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, AmbientGrade ctrl Γ i (xs j)) :
    AmbientGrade ctrl Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

theorem variableAssignmentBounded (ctrl : Nat → Nat) (Γ : List Ty) (τ : Ty) (p : Policy)
    (x : Variable Γ τ) : ∃ v : OrdinalVector Γ τ.level,
    assignment p (.var x) = some v ∧ (∀ j, AmbientGrade ctrl Γ j.val (v j)) ∧ SourceBoundedVector ctrl v := by
  refine ⟨fun j => .var ⟨τ, x, j⟩, rfl, fun j => .var x j, ?_⟩
  apply (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ _ _).mp
  intro ρ j
  exact ρ.bounded x j

theorem oneVectorBounded (ctrl : Nat → Nat) (Γ : List Ty) (m : Nat) :
    (∀ j : Fin (m+1), AmbientGrade ctrl Γ j.val (.one : OrdinalExpression Γ)) ∧
    SourceBoundedVector ctrl (fun _ : Fin (m+1) => (.one : OrdinalExpression Γ)) := by
  refine ⟨fun j => .one j.val, (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ m _).mp ?_⟩
  intro ρ j
  exact le_rfl

theorem recursorAssignmentBounded (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (p : Policy) :
    ∃ v : OrdinalVector Γ σ.recType.level, assignment p (.recC σ) = some v ∧
      (∀ j, AmbientGrade ctrl Γ j.val (v j)) ∧ SourceBoundedVector ctrl v := by
  let v : OrdinalVector Γ σ.recType.level := fun j =>
    if j.val = 0 then numeral p 2 else if j.val = σ.level + 2 then .omega else .one
  refine ⟨v, rfl, ?_, (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ _ v).mp ?_⟩
  · intro j
    dsimp only [v]
    split
    · exact expand_ambient ctrl (p.shape .numeral 1) (fun _ => .one) (fun _ => .one j.val)
    · split
      · rename_i hz he
        exact .omega j.val (by omega)
      · exact .one j.val
  · intro ρ j
    have hn : actualOrdinalNorm (expressionValue ctrl ρ (numeral p 2)) = 2 := by
      rw [numeral, SelectedNormSumsProof.repeatNorm ctrl Γ ρ p .numeral 2 .one (by decide), one_norm ctrl]
    have h0 : v 0 = numeral p 2 := by simp [v]
    rw [h0, hn]
    dsimp only [v]
    split
    · exact hn.le
    · split
      · rw [omega_norm ctrl]
      · rw [one_norm ctrl]; decide

end LogicLineages.PermittedControl.SelectedAtomicAssignmentProof
