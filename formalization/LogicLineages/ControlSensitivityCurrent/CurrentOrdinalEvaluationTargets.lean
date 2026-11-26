module
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics (Term)
open CurrentOrdinalEvaluation

def Calibration : Prop :=
  ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (ι : Type) (index : ι → Nat) (t : Term ι) (env : List Nat) (ρ : ι → Nat),
    (∀ x, env.getD (index x) 0 = ρ x) →
    ∃ a : NONote, evaluate f env (OrdinalSyntax.code index t) = rawNoteEncode a.1 ∧
      a.1.repr = ParametricSourceSuccessor.denoteWith f (fun x => (ρ x : Ordinal)) t

def Effective : Prop :=
  ∀ f : Nat → Nat, Computable f → FullAddition.Targets.SourceGrowth f →
    Computable (fun p : List Nat × Nat => evaluate f p.1 p.2)

end LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationTargets
