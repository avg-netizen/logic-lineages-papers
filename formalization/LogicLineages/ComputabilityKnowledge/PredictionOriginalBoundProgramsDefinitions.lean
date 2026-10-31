module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundsDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionMaximumDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundPrograms

def compile (u : Nat.Partrec.Code) (m : Nat) : Nat.Partrec.Code := Nat.Partrec.Code.curry u m

def CompilerSemantics (u : Nat.Partrec.Code) (g : Nat → Nat → Nat) : Prop :=
  ∀ m n : Nat, Nat.Partrec.Code.eval (compile u m) n = Part.some (PredictionOriginalBounds.levelBound g m n)

end LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundPrograms
