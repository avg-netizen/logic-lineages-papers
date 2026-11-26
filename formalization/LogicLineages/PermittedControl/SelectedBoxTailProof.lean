module
public import LogicLineages.PermittedControl.SelectedBoxPositiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedBoxTailProof
open OrdinalComparison Source SelectedSourceDomain
open Source.AdmissibleSum Source.AdmissibleAssignment Source.AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem expand_ambient (ctrl : Nat → Nat) {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, AmbientGrade ctrl Γ i (xs j)) :
    AmbientGrade ctrl Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

private theorem three_ambient (ctrl : Nat → Nat) {Γ : List Ty} {i : Nat} (p : Policy) (site : MacroSite)
    {a b c : OrdinalExpression Γ} (ha : AmbientGrade ctrl Γ i a)
    (hb : AmbientGrade ctrl Γ i b) (hc : AmbientGrade ctrl Γ i c) :
    AmbientGrade ctrl Γ i (three p site a b c) := by
  apply expand_ambient ctrl
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

private theorem one_norm (ctrl : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ) :
    actualOrdinalNorm (expressionValue ctrl ρ .one) = 1 := by
  simpa [expressionValue, ParametricSourceSuccessor.denoteWith] using (finiteNorm 1).2

private theorem add_norm (ctrl : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ) (f g : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ctrl ρ (.add f g)) =
      actualOrdinalNorm (expressionValue ctrl ρ f) + actualOrdinalNorm (expressionValue ctrl ρ g) :=
  Source.OriginalDomain.actualNaturalSumNormAdditivity _ _ (SelectedValueClosureProof.ambient_below ctrl ρ f)
    (SelectedValueClosureProof.ambient_below ctrl ρ g)

private theorem three_norm (ctrl : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ) (p : Policy)
    (site : MacroSite) (a b c : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ctrl ρ (three p site a b c)) =
      actualOrdinalNorm (expressionValue ctrl ρ a) + actualOrdinalNorm (expressionValue ctrl ρ b) +
        actualOrdinalNorm (expressionValue ctrl ρ c) := by
  unfold three
  rw [SelectedNormSumsProof.shapeNorm]
  simp [List.ofFn_succ, Nat.add_assoc]

theorem tailGradeAndNorm : SelectedBoxTargets.TailGradeAndNorm := by
  intro ctrl Γ p n f g hf hg
  by_cases hn : n = 0
  · subst n
    simp only [boxTail, if_pos rfl, Nat.add_zero]
    exact ⟨.add hf hg, fun ρ => add_norm ctrl ρ f g⟩
  · have hnum : AmbientGrade ctrl Γ 0 (numeral p n) := by
      cases n with
      | zero => contradiction
      | succ n => exact expand_ambient ctrl _ _ (fun _ => .one 0)
    rw [boxTail, if_neg hn]
    refine ⟨three_ambient ctrl p .optionalBoxTail hf hg hnum, ?_⟩
    intro ρ
    rw [three_norm ctrl, numeral, SelectedNormSumsProof.repeatNorm ctrl Γ ρ p .numeral n .one (by omega), one_norm ctrl]
    simp

end LogicLineages.PermittedControl.SelectedBoxTailProof
