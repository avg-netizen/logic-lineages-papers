module
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeStructureProof
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportPartialProof
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialProof
public import LogicLineages.OrdinalComparison.WWGeneratedSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.Proof
open ActiveScalarAnnotation AssignmentSupport AssignmentSupport.Proof AdmissibleSum

private theorem free_partial_trees {k Γ} (F : Variable Γ (Ty.curriedGround (k+1)))
    (p : Policy) (q : OrdinalExpression (.ground :: Γ)) (v : OrdinalPartialVector Γ .ground)
    (hq : ScalarTrees (.there F) q) (hf : ordinalHeadFree q = true)
    (hv : AdmissiblePartial.run p 0 q = some v) : ScalarTrees F (v 0) ∧ HeadTree F (v 1) := by
  rw [AdmissiblePartial.run.eq_def, if_pos hf] at hv
  cases hv
  exact ⟨.add (headClosureScalar k Γ F q hq) (scalar_one F), head_one F⟩

theorem groundPartialTrees : Targets.GroundPartialTrees := by
  intro k Γ F p q v hq
  induction hq generalizing v with
  | @free q hg hn =>
    intro hv
    obtain ⟨w, hw, hgrades⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ .ground p 0 q hg
    have he : w = v := Option.some.inj (hw.symm.trans hv)
    subst w
    have hinactive : ∀ j, ¬ Active F (v j) := by
      intro j ha
      have hm := actualPartialSupport Γ .ground p 0 q v hv j _ ha
      exact hn ((TrackedSource.Proof.mem_dropBound F (names q)).mp hm)
    exact ⟨.free (hgrades 0) (hinactive 0), .free (hgrades 1) (hinactive 1)⟩
  | tracked =>
    intro hv
    exact free_partial_trees F p _ v .tracked (by rfl) hv
  | @add a b ha hb iha ihb =>
    intro hv
    by_cases hf : ordinalHeadFree (.add a b) = true
    · exact free_partial_trees F p _ v (.add ha hb) hf hv
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hpa : AdmissiblePartial.run p 0 a with
      | none => simp [hpa] at hv
      | some pa =>
        cases hpb : AdmissiblePartial.run p 0 b with
        | none => simp [hpa, hpb] at hv
        | some pb =>
          simp [hpa, hpb] at hv
          subst v
          have hta := iha pa hpa
          have htb := ihb pb hpb
          constructor
          · unfold AdmissiblePartial.three
            apply scalar_expand
            intro j
            split_ifs
            · exact hta.1
            · exact htb.1
            · exact scalar_one F
          · unfold AdmissiblePartial.three
            apply head_expand
            intro j
            split_ifs
            · exact hta.2
            · exact htb.2
            · exact head_one F
  | @collapse h t hh ht ih =>
    intro hv
    by_cases hf : ordinalHeadFree (.collapse h t) = true
    · exact free_partial_trees F p _ v (.collapse hh ht) hf hv
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hph : AdmissiblePartial.run p 1 h with
      | none => simp [hph] at hv
      | some ph =>
        cases hpt : AdmissiblePartial.run p 0 t with
        | none => simp [hph, hpt] at hv
        | some pt =>
          simp [hph, hpt] at hv
          subst v
          have htt := ih pt hpt
          have hfh : ordinalHeadFree h = true :=
            actualGeneratedHeadFreeAbove Γ .ground 1 h (head_grade hh) (by decide)
          rw [AdmissiblePartial.run.eq_def, if_pos hfh] at hph
          have hph' : ph = ordinalFreePartialVector 1 h := (Option.some.inj hph).symm
          constructor
          · exact .collapse (headClosureHead k Γ F h hh) htt.1
          · change HeadTree F (.add (ph 1) (pt 1))
            rw [hph']
            exact .add (.add (headClosureHead k Γ F h hh) (head_one F)) htt.2

end LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.Proof
