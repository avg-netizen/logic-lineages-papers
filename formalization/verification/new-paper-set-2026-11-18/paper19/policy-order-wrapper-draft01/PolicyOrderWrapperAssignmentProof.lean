module
public import LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapperTargets
public import LogicLineages.ControlSensitivityCurrent.FullCollisionProof
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapper
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence ParametricSourceSuccessor
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
private theorem shape0 (p : AdmissibleSum.Policy) (site : AdmissibleSum.MacroSite) :
    p.shape site 0 = .leaf := PolicyGadget.smallShapes.2.1 _
private theorem shape1 (p : AdmissibleSum.Policy) (site : AdmissibleSum.MacroSite) :
    p.shape site 1 = .join .leaf .leaf := PolicyGadget.smallShapes.2.2 _
def three {Γ} : OrdinalExpression Γ := .add (.add .one .one) .one
def five {Γ} : OrdinalExpression Γ := .add (.add (.add .one .one) (.add .one .one)) .one

theorem identity_application (p : AdmissibleSum.Policy) {Γ} (t : OriginalTerm Γ .ground) (v : OrdinalVector Γ 0)
    (hv : AdmissibleAssignment.assignment p t=some v) :
    AdmissibleAssignment.assignment p (.app identity t)=
      some (fun _ => .collapse .one (.add three (v 0))) := by
  change (AdmissibleAssignment.assignment p identity >>= fun f =>
    AdmissibleAssignment.assignment p t >>= fun a =>
      some (AdmissibleAssignment.application p f a)) = _
  rw [hv]
  apply congrArg some
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  simp only [Ty.level,List.ofFn_succ,List.ofFn_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only [AdmissibleAssignment.application,AdmissibleAssignment.box,Ty.level,Fin.val_zero]
  rw [ordinalBoxPositive]
  simp only [show ¬ (1 ≤ 0) by omega,dite_false]
  simp [Fin.cases_zero,three,AdmissibleAssignment.boxTail,Ty.level,ordinalVectorAt,
    ordinalPartialSize,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs,
    ordinalHeadClosure,ordinalHeadClosureComponent,substitute,AdmissibleAssignment.repeated,
    shape0,shape1,AdmissibleSum.expand]
  all_goals repeat' constructor

theorem constant_application (p : AdmissibleSum.Policy) {Γ} (t : OriginalTerm Γ .ground) (v : OrdinalVector Γ 0)
    (hv : AdmissibleAssignment.assignment p t=some v) :
    AdmissibleAssignment.assignment p (.app constant t)=
      some (fun _ => .collapse .one (.add five (v 0))) := by
  change (AdmissibleAssignment.assignment p constant >>= fun f =>
    AdmissibleAssignment.assignment p t >>= fun a =>
      some (AdmissibleAssignment.application p f a)) = _
  rw [hv]
  apply congrArg some
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  simp only [Ty.level,List.ofFn_succ,List.ofFn_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only [AdmissibleAssignment.application,AdmissibleAssignment.box,Ty.level,Fin.val_zero]
  rw [ordinalBoxPositive]
  simp only [show ¬ (1 ≤ 0) by omega,dite_false]
  simp [Fin.cases_zero,five,AdmissibleAssignment.boxTail,Ty.level,ordinalVectorAt,
    ordinalPartialSize,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs,
    ordinalFreePartialVector,ordinalHeadClosure,ordinalHeadClosureComponent,substitute,
    AdmissibleAssignment.repeated,shape0,shape1,AdmissibleSum.expand]
  all_goals repeat' constructor

end LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapper
