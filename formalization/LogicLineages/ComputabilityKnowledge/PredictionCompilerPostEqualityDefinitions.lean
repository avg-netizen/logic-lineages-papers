module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEqualityDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEqualityDefinitions
@[expose] public section
/-! Extensional Boolean comparison for actual compiled TM1 statements and
TM0 labels, using explicit finite input-domain comparisons. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEquality
open Turing PredictionCompilerTapeSupport PredictionCompilerLabelEquality PredictionCompilerAlphabetEquality

def directionEq : Dir → Dir → Bool
  | .left, .left => true
  | .right, .right => true
  | _, _ => false

def tapeEq : TapeStatement → TapeStatement → Bool
  | .move d q, .move e r => directionEq d e && tapeEq q r
  | .write f q, .write g r => sameInputs workEq f g && tapeEq q r
  | .load f q, .load g r => sameInputs (fun a b : Store => decide (a = b)) f g && tapeEq q r
  | .branch f q₁ q₂, .branch g r₁ r₂ =>
    sameInputs (fun a b : Bool => decide (a = b)) f g && tapeEq q₁ r₁ && tapeEq q₂ r₂
  | .goto f, .goto g => sameInputs labelEq f g
  | .halt, .halt => true
  | _, _ => false

def optionalTapeEq : Option TapeStatement → Option TapeStatement → Bool
  | none, none => true
  | some q, some r => tapeEq q r
  | _, _ => false

def postEq (a b : PostLabel) : Bool := optionalTapeEq a.1 b.1 && decide (a.2 = b.2)

end LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEquality
