module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationDefinitions
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentDefinitions
public import LogicLineages.OrdinalComparison.WWAbsoluteProbeDAGDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAbsolute

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence

def vectorDigits (p : AdmissibleSum.Policy) (d : RawSourceDAG.Code) : List Nat :=
  (PolicyAssignment.assignmentCode p d.1 (CurrentTreeCode.expand d)).getD []

noncomputable def anchor (p : AdmissibleSum.Policy) (f : Nat → Nat) (d : RawSourceDAG.Code) : Nat :=
  encodedFiniteValue (CurrentOrdinalEvaluation.evaluate f
    (SourceGroundComponentEnvironment.environment (List.replicate d.1.length 1))
    ((vectorDigits p d).getD 0 0))

def Scalar (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ τ) (v : Nat) : Prop :=
  ∃ w : OrdinalVector Γ τ.level, AdmissibleAssignment.assignment p t = some w ∧
    ParametricSourceSuccessor.denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (w 0) = (v : Ordinal)

noncomputable def Formula (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (hg : ∀ σ ∈ Γ, σ = Ty.ground) (d : Input Γ τ)
    (ρ : OrdinalComponent Γ → Nat) (v : Nat) : Prop :=
  ∃ x y : Nat,
    let σ := AbsoluteObserver.extend ρ x y
    PolicyCollision.rawScalar p f σ (AbsoluteProbeDAG.originalInput d).term =
      PolicyCollision.rawScalar p f σ (AbsoluteProbeDAG.closedInput hg d).term ∧
    AbsoluteObserver.factor τ * v + (x+1) = AbsoluteObserver.factor τ *
      anchor p f (RawSourceDAG.encode ⟨Γ,τ,d⟩) + (y+1)

end LogicLineages.ControlSensitivityCurrent.CurrentAbsolute
