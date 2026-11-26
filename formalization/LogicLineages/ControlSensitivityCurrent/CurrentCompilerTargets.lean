module
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCompilerTargets

open LogicLineages.OrdinalComparison.Source
open RawSourceDAG.InputCompiler (InputCode encodeInput)
open RawSourceDAG.PlanComparison (OutputCode)
open CurrentCompiler

def Effective : Prop :=
  Computable (fun p : Nat × InputCode => run p.1 p.2) ∧ Computable compile

def LiteralOutputs : Prop :=
  (∀ (n : Nat) (q : InputNormalization.Input (List.replicate n Ty.ground) 0),
    run n (encodeInput q) = some (expected q) ∧ compile (n,encodeInput q) = expected q) ∧
  ∀ s : SourceAST.Sentence,
    compile (s.variables,encodeInput s.matrix.toInput) =
      (RawPlanComparisonTargets.encodeComparison (BooleanCompiler.strictPair s.matrix.toProgram),
        RawPlanComparisonTargets.encodeComparison (BooleanCompiler.weakPair s.matrix.toProgram))

def ValidCodes : Prop :=
  (∀ (n : Nat) (code : InputCode) (out : OutputCode), run n code = some out →
    ∃ q : InputNormalization.Input (List.replicate n Ty.ground) 0,
      encodeInput q = code ∧ out = expected q) ∧
  ∀ (n : Nat) (code : InputCode),
    run n code = none ↔ ¬ ∃ q : InputNormalization.Input (List.replicate n Ty.ground) 0,
      encodeInput q = code

/-- Current paper19 thm:compiler for the genuine existential ground-input source grammar. -/
def CompleteCompiler : Prop :=
  Effective ∧ LiteralOutputs ∧ ValidCodes ∧
  CompilerCompositionTargets.ASTCorrect ∧ CompilerCompositionTargets.SharedCorrect ∧
  CompilerCompositionTargets.Retention ∧ CompilerCompositionTargets.OutputBudgets

end LogicLineages.ControlSensitivityCurrent.CurrentCompilerTargets
