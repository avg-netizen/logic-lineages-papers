module
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetTargets
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusProof
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeStructureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.Proof
open AdditiveHeadTree HeadFiniteSurplus
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem scalarSecond_pos {Γ σ} (q : OrdinalExpression (σ :: Γ)) : 1 ≤ scalarSecond q := by
  cases q with
  | var _ | zero | one | omega | emul _ _ => simp [scalarSecond]
  | add a b => simp only [scalarSecond]; split <;> omega
  | collapse h t =>
    have hp := HeadFiniteSurplus.Proof.secondCount_positive h
    simp only [scalarSecond]
    split <;> omega

theorem scalarSecond_of_free {Γ σ} (q : OrdinalExpression (σ :: Γ))
    (hf : ordinalHeadFree q = true) : scalarSecond q = 1 := by
  cases q <;> simp [scalarSecond,hf]

private theorem free_second {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (hf : ordinalHeadFree q = true)
    (hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v)
    (ν : OrdinalComponent Γ → Ordinal) :
    denote ν (v (outputTwo k)) = (scalarSecond q : Ordinal) := by
  rw [AdmissiblePartial.run.eq_def, if_pos hf] at hv
  cases hv
  rw [scalarSecond_of_free q hf]
  simp [ordinalFreePartialVector,outputTwo,denote]

theorem scalarSecond_of_run {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ht : ScalarTrees (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v)
    (ν : OrdinalComponent Γ → Ordinal) :
    denote ν (v (outputTwo k)) = (scalarSecond q : Ordinal) := by
  induction ht generalizing v with
  | @free q grade inactive =>
    exact free_second q v (HeadFiniteSurplus.Proof.headFree_of_inactive q inactive) hv ν
  | tracked =>
    rw [AdmissiblePartial.run.eq_def] at hv
    simp [ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs] at hv
    subst v
    simp [denote,scalarSecond]
  | @add a b ha hb iha ihb =>
    by_cases hf : ordinalHeadFree (.add a b) = true
    · exact free_second _ v hf hv ν
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hva : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 a with
      | none => simp [hva] at hv
      | some va =>
        cases hvb : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 b with
        | none => simp [hva,hvb] at hv
        | some vb =>
          simp [hva,hvb] at hv
          subst v
          rw [HeadFiniteSurplus.Proof.three_value, iha va hva, ihb vb hvb]
          simpa [denote,scalarSecond,hf] using
            HeadFiniteSurplus.Proof.finite_count_add (scalarSecond a) (scalarSecond b)
  | @collapse h t hh ht ih =>
    by_cases hf : ordinalHeadFree (.collapse h t) = true
    · exact free_second _ v hf hv ν
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hvh : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 1 h with
      | none => simp [hvh] at hv
      | some vh =>
        cases hvt : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 t with
        | none => simp [hvh,hvt] at hv
        | some vt =>
          simp [hvh,hvt] at hv
          subst v
          obtain ⟨vh',hvh',heh⟩ := HeadFiniteSurplus.Proof.exactHeadPartial k Γ OrdinalSyntax.defaultPolicy h hh
          have hev : vh' = vh := Option.some.inj (hvh'.symm.trans hvh)
          subst vh'
          change ordinalNaturalSum (denote ν (vh (outputTwo k))) (denote ν (vt (outputTwo k))) = _
          rw [(heh ν).2,ih vt hvt]
          simpa [scalarSecond,hf] using naturalSum_finite (secondCount h) (scalarSecond t)

theorem exactScalarSecond : Targets.ExactScalarSecond := by
  intro k Γ q ht
  obtain ⟨v,hv,hg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ
    (Ty.curriedGround (k+1)) OrdinalSyntax.defaultPolicy 0 q (AdditiveHeadTree.Proof.scalar_grade ht)
  exact ⟨v,hv,scalarSecond_pos q,scalarSecond_of_run q ht v hv⟩

end LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.Proof
