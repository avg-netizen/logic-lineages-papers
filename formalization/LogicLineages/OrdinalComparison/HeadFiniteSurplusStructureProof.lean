module
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusTargets
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeStructureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Proof
open AdditiveHeadTree ActiveScalarAnnotation AssignmentSupport AssignmentSupport.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem headFree_of_inactive {k Γ}
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (hn : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) h) :
    ordinalHeadFree h = true := by
  induction h with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => exact False.elim (hn (by simp [Active, componentName]))
    | there x => rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    have hn' : ¬ (Active .here a ∨ Active .here b) := by
      simpa only [Active, names_add, names_emul, names_collapse, List.mem_append] using hn
    have ha : ¬ Active .here a := fun ha => hn' (Or.inl ha)
    have hb : ¬ Active .here b := fun hb => hn' (Or.inr hb)
    have hfa := iha ha
    have hfb := ihb hb
    simp only [ordinalHeadFree, Bool.not_eq_true] at hfa hfb ⊢
    simp [ordinalHeadOccurs, hfa, hfb]

theorem surplus_of_free {Γ σ} (h : OrdinalExpression (σ :: Γ))
    (hf : ordinalHeadFree h = true) : surplus h = 1 := by
  cases h <;> simp [surplus, hf]

theorem secondCount_of_free {Γ σ} (h : OrdinalExpression (σ :: Γ))
    (hf : ordinalHeadFree h = true) : secondCount h = 1 := by
  cases h <;> simp [secondCount, hf]

theorem secondCount_positive {Γ σ} (h : OrdinalExpression (σ :: Γ)) :
    0 < secondCount h := by
  cases h <;> simp only [secondCount] <;> first | omega | (split <;> omega)

theorem surplusBounds : Targets.SurplusBounds := by
  intro k Γ h ht
  have hz : surplus h = 0 ↔ h = .var ⟨_,.here,UnaryCarrier.headIndex k⟩ := by
    induction ht with
    | @free h hg hn =>
      have hf := headFree_of_inactive h hn
      constructor
      · rw [surplus_of_free h hf]
        omega
      · intro he
        subst h
        simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs] at hf
    | tracked => simp [surplus, ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
    | @add a b ha hb iha ihb =>
      simp only [surplus]
      split <;> simp
  refine ⟨secondCount_positive h, hz, ?_⟩
  intro ν hlarge
  by_contra hn
  have hzero : surplus h = 0 := by omega
  have he := hz.mp hzero
  subst h
  have hone : Ordinal.omega0 ≤ (1 : Ordinal) := by
    simpa [ordinalHeadClosure, substitute, ordinalHeadClosureComponent, denote] using hlarge
  have hlt : (1 : Ordinal) < Ordinal.omega0 := by simpa using Ordinal.natCast_lt_omega0 1
  exact (not_le_of_gt hlt) hone

end LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Proof
