module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationShapeProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetFloorProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation

open LogicLineages.OrdinalComparison.Source
open AdmissibleSum ScalarAnnotationData ActiveScalarAnnotation AdditiveHeadTree

private theorem freePartial (p : Policy) {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) (hd : Valid p d)
    (hf : ordinalHeadFree (erase d) = true) :
    ∃ (v : OrdinalPartialVector Γ .ground) (e : Tree k Γ F),
      AdmissiblePartial.run p 0 (erase d) = some v ∧ groundPartial p d = some e ∧
      erase e = v 0 ∧ Valid p e := by
  refine ⟨ordinalFreePartialVector 0 (erase d),.add (closeTree d) (.free .one),?_,?_,?_,?_⟩
  · rw [AdmissiblePartial.run.eq_def,if_pos hf]
  · rw [groundPartial.eq_def,if_pos hf]
  · change (.add (erase (closeTree d)) .one : OrdinalExpression Γ) =
      .add (ordinalHeadClosure (erase d)) .one
    rw [ScalarAnnotationData.Proof.close_erase]
  · exact ⟨closeValid p d hd,oneValid p⟩

theorem typedGroundPartial (p : Policy) {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) (hd : Valid p d) :
    ∃ (v : OrdinalPartialVector Γ .ground) (e : Tree k Γ F),
      AdmissiblePartial.run p 0 (erase d) = some v ∧ groundPartial p d = some e ∧
      erase e = v 0 ∧ Valid p e := by
  induction d with
  | free q =>
    by_cases hf : ordinalHeadFree (erase (Tree.free (k := k) (F := .there F) q)) = true
    · exact freePartial p _ hd hf
    obtain ⟨v,hv,hg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ .ground p 0 q hd.1
    refine ⟨v,.free (v 0),hv,?_,rfl,hg 0,?_⟩
    · rw [groundPartial.eq_def,if_neg hf]
      simp [hv]
    · exact fun ha => hd.2 ((CurrentGroundBudget.groundPartialActivity p F q v hv).1 ha)
  | tracked => exact freePartial p _ hd rfl
  | add a b iha ihb =>
    by_cases hf : ordinalHeadFree (erase (.add a b)) = true
    · exact freePartial p _ hd hf
    obtain ⟨va,oa,hva,hoa,hea,hda⟩ := iha hd.1
    obtain ⟨vb,ob,hvb,hob,heb,hdb⟩ := ihb hd.2
    refine ⟨(fun j => AdmissiblePartial.three p .activeAdd (va j) (vb j) .one),
      threeTree p oa ob,?_,?_,?_,threeValid p oa ob hda hdb⟩
    · rw [AdmissiblePartial.run.eq_def,if_neg hf]
      simp only [erase,hva,hvb,Option.bind_some,pure]
      rfl
    · rw [groundPartial.eq_def,if_neg hf]
      simp only [hoa,hob,Option.bind_some,pure]
      rfl
    · rw [threeErase,hea,heb]
  | collapse op tail ih =>
    by_cases hf : ordinalHeadFree (erase (.collapse op tail)) = true
    · exact freePartial p _ hd hf
    obtain ⟨pt,out,hpt,hout,het,hdt⟩ := ih hd.2.2.2
    have hheadfree : ordinalHeadFree op.head = true :=
      actualGeneratedHeadFreeAbove Γ .ground 1 op.head (AdditiveHeadTree.Proof.head_grade hd.2.1) (by decide)
    have hph : AdmissiblePartial.run p 1 op.head = some (ordinalFreePartialVector 1 op.head) := by
      rw [AdmissiblePartial.run.eq_def,if_pos hheadfree]
    let v : OrdinalPartialVector Γ .ground := fun j => if j.val = 0 then
      .collapse (ordinalHeadClosure op.head) (pt 0)
      else .add (ordinalFreePartialVector 1 op.head j) (pt j)
    refine ⟨v,.collapse (closeOperator op) out,?_,?_,?_,?_⟩
    · rw [AdmissiblePartial.run.eq_def,if_neg hf]
      simp only [erase,hph,hpt,if_pos rfl,Option.bind_some,pure]
      rfl
    · rw [groundPartial.eq_def,if_neg hf]
      simp only [hout,Option.bind_some,pure]
      rfl
    · change (.collapse (ordinalHeadClosure op.head) (erase out) : OrdinalExpression Γ) =
        .collapse (ordinalHeadClosure op.head) (pt 0)
      rw [het]
    · refine ⟨closeOperatorAssignment p op hd.1,
        AdditiveHeadTree.Proof.headClosureHead k Γ F op.head hd.2.1,?_,hdt⟩
      intro hh
      have hhold := (ActiveScalarAnnotation.Proof.active_headClosure F op.head).1 hh
      have htail := hd.2.2.1 hhold
      change Active F (erase out)
      rw [het]
      exact (CurrentGroundBudget.groundPartialActivity p F (erase tail) pt hpt).2 htail

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation
