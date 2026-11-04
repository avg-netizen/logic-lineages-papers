module
public import LogicLineages.OrdinalComparison.SourceMachineInternalLevelTargets
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsProof
public import LogicLineages.OrdinalComparison.SourceMachinePlanFragmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineInternalLevel.Proof
open SourceGroundBinderFragment SourceMachineRawValuations SourceClasses SourceTypeSupport

private theorem subtype_level (τ σ : Ty) (h : σ ∈ τ.subtypes) : σ.level ≤ τ.level := by
  induction τ with
  | ground =>
    have hs : σ=Ty.ground := by simpa [Ty.subtypes] using h
    subst σ
    exact le_rfl
  | arrow a b iha ihb =>
    simp only [Ty.subtypes,List.mem_cons,List.mem_append] at h
    rcases h with rfl | h | h
    · exact le_rfl
    · exact (iha h).trans ((Nat.le_succ _).trans (Nat.le_max_left _ _))
    · exact (ihb h).trans (Nat.le_max_right _ _)

private theorem bound_leaf {Γ τ} (t : OriginalTerm Γ τ)
    (ht : typeSupport t=τ.subtypes.toFinset) (hτ : τ.level≤1) : InternalLevelBound 1 t := by
  intro σ hσ
  rw [ht] at hσ
  exact (subtype_level τ σ (List.mem_toFinset.mp hσ)).trans hτ

private theorem structural_pair {Γ τ} (t : OriginalTerm Γ τ) :
    AllGround Γ → Fragment t → τ.level≤1 ∧ InternalLevelBound 1 t := by
  induction t with
  | var x =>
    intro hΓ h
    have ht := SourceMachineRawValuations.Proof.variable_ground hΓ x
    cases ht
    exact ⟨by decide,bound_leaf _ (by simp [typeSupport]) (by decide)⟩
  | app f a ihf iha =>
    rintro hΓ ⟨hf,ha⟩
    have hff := ihf hΓ hf
    have haa := iha hΓ ha
    have ht : _ := (Nat.le_max_right _ _).trans hff.1
    refine ⟨ht,?_⟩
    intro σ hσ
    rcases Finset.mem_union.mp hσ with h | h
    · exact (subtype_level _ σ (List.mem_toFinset.mp h)).trans ht
    · rcases Finset.mem_union.mp h with h | h
      · exact hff.2 σ h
      · exact haa.2 σ h
  | @lam Γ σ τ body ih =>
    rintro hΓ ⟨hs,hb⟩
    subst σ
    have hctx : AllGround (Ty.ground::Γ) := by
      intro υ hυ
      rcases List.mem_cons.mp hυ with h | h
      · exact h
      · exact hΓ υ h
    have hh := ih hctx hb
    have ht : (Ty.arrow Ty.ground τ).level≤1 := by
      change max (0+1) τ.level≤1
      exact max_le (by decide) hh.1
    refine ⟨ht,?_⟩
    intro υ hυ
    rcases Finset.mem_union.mp hυ with h | h
    · exact (subtype_level _ υ (List.mem_toFinset.mp h)).trans ht
    · exact hh.2 υ h
  | zeroC =>
    intro _ _
    exact ⟨by decide,bound_leaf _ (by simp [typeSupport]) (by decide)⟩
  | succC =>
    intro _ _
    exact ⟨by decide,bound_leaf _ (by simp [typeSupport]) (by decide)⟩
  | caseC τ => intro _ h; exact False.elim h
  | recC τ => intro _ h; exact False.elim h
  | ranked s args ih => exact nomatch s

theorem structuralLevel : Targets.StructuralLevel := by
  intro Γ τ t hΓ ht
  exact (structural_pair t hΓ ht).2

theorem actualAggregateLevel : Targets.ActualAggregateLevel := by
  intro b e
  have hg := SourceMachineRawValuations.Proof.groundContexts.2 b e
  have hf := (SourceMachinePlanFragment.Proof.actualAggregateFragment b e).2
  exact ⟨structuralLevel _ _ _ hg hf.1,structuralLevel _ _ _ hg hf.2⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineInternalLevel.Proof
