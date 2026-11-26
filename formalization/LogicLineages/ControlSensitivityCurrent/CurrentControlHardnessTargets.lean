module
public import LogicLineages.ControlSensitivityCurrent.CurrentControlHardnessDefinitions
public import LogicLineages.ControlSensitivityCurrent.ActualParityTargets
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentControlHardnessTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open CurrentControlHardness

def ExactLowering : Prop :=
  ∀ b (p : AdmissibleSum.Policy) (strict : Bool),
    Primrec (output strict b) ∧ ∀ e,
      output strict b e = SourceMachineQueryCode.pack ((ctx b e).length,
        SyntaxCode.encodeTerm (dagPair strict b e).1.term, SyntaxCode.encodeTerm (dagPair strict b e).2.term) ∧
      SourceGammaRestrictedReduction.RestrictedSyntax (output strict b e) ∧
      (member strict p b (output strict b e) ↔ ¬ SourceBlankMachineSimulation.Halts e)

def ActualDAGBound : Prop :=
  ∀ b e (strict : Bool),
    (dagPair strict b e).1.specs.length ≤ 250 * (e + 4 * SourceMachineConjunctionPlan.bits b + 27) + 24 ∧
    (dagPair strict b e).2.specs.length ≤ 250 * (e + 4 * SourceMachineConjunctionPlan.bits b + 27) + 24

def Completeness : Prop :=
  ∀ b (p : AdmissibleSum.Policy), LogicLineages.StandardControlCurrent.PolicyShape.Effective p →
    ∀ strict : Bool, REPred (fun n => ¬ member strict p b n) ∧
      ∀ P : Nat → Prop, REPred (fun n => ¬ P n) → ManyOneReducible P (member strict p b)

def Full : Prop := ExactLowering ∧ ActualDAGBound ∧ Completeness ∧ ActualParityTargets.NonEventualPeriodicity

end LogicLineages.ControlSensitivityCurrent.CurrentControlHardnessTargets
