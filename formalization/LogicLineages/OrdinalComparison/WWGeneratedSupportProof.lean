module
public import LogicLineages.OrdinalComparison.WWGeneratedSupportTargets
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem actualGeneratedComponentIndex : Targets.ActualGeneratedComponentIndex := by
  intro Γ i t h
  induction h with
  | one i => simp [ordinalExpressionVariables]
  | omega i hi => simp [ordinalExpressionVariables]
  | var v k => simp [ordinalExpressionVariables]
  | add hf hg ihf ihg =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ihf c hc
    · exact ihg c hc
  | emul hi hf hg ihf ihg =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (Nat.le_succ _).trans (ihf c hc)
    · exact ihg c hc
  | collapse hf hg ihf ihg => intro c hc; exact Nat.zero_le _

private theorem head_free_of_components {Γ : List Ty} {σ : Ty}
    (t : OrdinalExpression (σ :: Γ))
    (h : ∀ c ∈ ordinalExpressionVariables t, ordinalHeadComponentOccurs c = false) :
    ordinalHeadFree t = true := by
  induction t with
  | var c =>
    have hc := h c (by simp [ordinalExpressionVariables])
    simp [ordinalHeadFree, ordinalHeadOccurs, hc]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
    have hf := ihf (fun c hc => h c (List.mem_append_left _ hc))
    have hg := ihg (fun c hc => h c (List.mem_append_right _ hc))
    simp [ordinalHeadFree] at hf hg
    simp [ordinalHeadFree, ordinalHeadOccurs, hf, hg]

theorem actualGeneratedHeadFreeAbove : Targets.ActualGeneratedHeadFreeAbove := by
  intro Γ σ i t ht hi
  apply head_free_of_components t
  intro c hc
  have hbound := actualGeneratedComponentIndex (σ :: Γ) i t ht c hc
  rcases c with ⟨τ, v, k⟩
  cases v with
  | here =>
    have hk := k.isLt
    simp only at hbound
    omega
  | there v => rfl

private theorem variable_type_mem {Γ : List Ty} {σ : Ty} (v : Variable Γ σ) : σ ∈ Γ := by
  induction v with
  | here => simp
  | there v ih => exact List.mem_cons_of_mem _ ih

theorem actualGeneratedGroundPositiveClosed : Targets.ActualGeneratedGroundPositiveClosed := by
  intro Γ hΓ i t hi ht
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c hc
  have hbound := actualGeneratedComponentIndex Γ i t ht c hc
  rcases c with ⟨τ, v, k⟩
  have hτ := hΓ τ (variable_type_mem v)
  subst τ
  have hk := k.isLt
  change k.val < 1 at hk
  simp only at hbound
  omega

end LogicLineages.OrdinalComparison.Source
