module
public import LogicLineages.PermittedControl.SelectedOmegaSeedTargets
public import LogicLineages.PermittedControl.SelectedHardnessCombinatorSyntaxProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
open OrdinalComparison Source Source.AdmissibleAssignment SelectedSourceDomain
open Source.FunctionalDetector (unary)
open Source.FunctionalHardnessCompletion.OmegaSeed (higherUnary higherIdentity higherLift source)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def identityVector (policy : AdmissibleSum.Policy) (Γ : List Ty) : OrdinalVector Γ 2 := fun j =>
  if j.val=0 then .add (repeated policy .scalarRepeat 8 .one) .one
  else if j.val=1 then .add (.add .one .one) .one else .add .one .one

theorem identity_assignment (policy : AdmissibleSum.Policy) (Γ : List Ty) :
    assignment policy (@higherIdentity Γ) = some (identityVector policy Γ) := by
  apply congrArg some
  funext j
  fin_cases j <;>
    simp [higherIdentity, assignment, abstraction, collect, identityVector, Ty.level,
      unary, higherUnary, AdmissiblePartial.run, ordinalPartialSize, ordinalHeadFree,
      ordinalHeadOccurs, ordinalHeadComponentOccurs, ordinalHeadClosure,
      ordinalHeadClosureComponent, substitute, repeated, SelectedHardnessUnusedProof.shape1,
      ControlSensitivityCurrent.PolicyGadget.smallShapes.2.1, AdmissibleSum.expand]
  all_goals dsimp [OrdinalPartialVector, Ty.level]
  all_goals simp [SelectedHardnessUnusedProof.shape1, AdmissibleSum.expand]

def higherVector (policy : AdmissibleSum.Policy) {Γ} (av : OrdinalVector Γ 2) : OrdinalVector Γ 2 :=
  application (σ:=.arrow .ground higherUnary) (τ:=higherUnary) policy
    (application (σ:=.ground) (τ:=.arrow (.arrow .ground higherUnary) higherUnary)
      policy
      (fun i => if i.val=0 then numeral policy 2
        else if i.val=3 then .omega else .one) (fun _ => .one))
    (SelectedHardnessUnusedProof.unusedVector policy av)

theorem higher_assignment (policy : AdmissibleSum.Policy) {Γ} (a : OriginalTerm Γ higherUnary) (av : OrdinalVector Γ 2)
    (ha : assignment policy a = some av) :
    assignment policy (higherLift a) = some (higherVector policy av) :=
  SelectedHardnessCombinatorSyntaxProof.app_assignment policy _ _ _ _
    (SelectedHardnessCombinatorSyntaxProof.app_assignment policy _ _ _ _ rfl rfl)
    (SelectedHardnessUnusedProof.unused_assignment policy a av ha)

theorem higher_head_expression (policy : AdmissibleSum.Policy) {Γ} (av : OrdinalVector Γ 2) :
    higherVector policy av 2 = .emul .omega (.add .one (.add (av 2) (av 2))) := by
  simp [higherVector, application, box, ordinalBoxPositive, ordinalVectorAt,
    SelectedHardnessUnusedProof.unusedVector, SelectedHardnessUnusedProof.freePart,
    unary, higherUnary, Ty.level, SelectedHardnessUnusedProof.shape1,
    ControlSensitivityCurrent.PolicyGadget.smallShapes.2.1, AdmissibleSum.expand]
  rfl

end LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
