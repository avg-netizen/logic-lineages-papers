module

public import LogicLineages.ComputabilityKnowledge.PredictionSecondJumpDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSecondJumpTargets
open PredictionLearning PredictionCanonicalList PredictionRelativeSelection PredictionMaximum
open PredictionSecondJump

def SecondJumpTotalityDecision : Prop := ComputableIn secondJumpOracles totalIndicator

def SecondJumpEqualityDecision : Prop := ComputableIn secondJumpOracles equalityIndicator

def SecondJumpCanonicalSelection : Prop := ComputableIn secondJumpOracles canonicalIndex

def SecondJumpCanonicalPrefix : Prop :=
  ComputableIn secondJumpOracles (fun m => Encodable.encode (canonicalPrefix m))

def UniformSecondJumpMaximumIndices : Prop :=
  ∃ universal : Code, CompilerSemantics universal ∧
    ComputableIn secondJumpOracles (compiledBoundIndex universal) ∧
    ∀ m : Nat, 1 ≤ m →
      TotalNat (Denumerable.ofNat Code (compiledBoundIndex universal m)) ∧
      ∀ n : Nat, Nat.Partrec.Code.eval (Denumerable.ofNat Code (compiledBoundIndex universal m)) n =
        Part.some (canonicalBound m n)

def FullCanonicalList : Prop :=
  ComputableIn secondJumpOracles canonicalIndex ∧
    StrictMono canonicalIndex ∧
    (∀ n : Nat, Representative (canonicalIndex n) ∧ TotalNat (canonicalCode n)) ∧
    (∀ c : Code, TotalNat c → ∃! n : Nat, SameFunction (canonicalCode n) c) ∧
    (∀ f : Nat → Nat, Computable f →
      ∃! n : Nat, ∀ x : Nat, Nat.Partrec.Code.eval (canonicalCode n) x = Part.some (f x)) ∧
    UniformSecondJumpMaximumIndices

end LogicLineages.ComputabilityKnowledge.PredictionSecondJumpTargets
