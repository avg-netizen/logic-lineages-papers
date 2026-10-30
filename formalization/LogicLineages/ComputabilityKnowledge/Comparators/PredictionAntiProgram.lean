module

public import LogicLineages.ComputabilityKnowledge.PredictionAntiProgram

@[expose] public section

/-! Independent exact uniform ordinary-program supplier for paper14
lem:finitevalues, first paragraph. The accepted antiEvader semantics is
unchanged. This target supplies actual computability/totality, not runtime
domination, total-function enumeration, or full finite measure values. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.PredictionAntiProgram

open LogicLineages.ComputabilityKnowledge.PredictionLearning
open LogicLineages.ComputabilityKnowledge.PredictionGame
open LogicLineages.ComputabilityKnowledge.PredictionAntiProgram

def PartialPrefixRecursive : Prop :=
  Partrec (fun x : Code × Nat => partialAntiPrefix x.1 x.2)

def PartialAntiRecursive : Prop :=
  Partrec (fun x : Code × Nat => antiProgram x.1 x.2)

def CodeSemantics (universal : Code) : Prop :=
  ∀ (p : Code) (input : Nat),
    Nat.Partrec.Code.eval (compiledAnti universal p) input = antiProgram p input

def UniformAntiCompiler : Prop :=
  ∃ universal : Code,
    Computable (compiledAnti universal) ∧ CodeSemantics universal ∧
    ∀ (p : Code) (hp : TotalBinary p),
      ∃ he : TotalBinary (compiledAnti universal p),
        policy (compiledAnti universal p) he = antiEvader (policy p hp) ∧
        (∀ n : Nat,
          prediction (policy p hp) (policy (compiledAnti universal p) he) n ≠
            evasion (policy p hp) (policy (compiledAnti universal p) he) n) ∧
        ¬ Learns (policy p hp) (policy (compiledAnti universal p) he)

def Target : Prop :=
  PartialPrefixRecursive ∧ PartialAntiRecursive ∧ UniformAntiCompiler

end LogicLineages.ComputabilityKnowledge.Comparators.PredictionAntiProgram
