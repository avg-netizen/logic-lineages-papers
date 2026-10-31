module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEqualityDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEqualityTargets
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionCompilerLabelEquality

def ExactStoreComparison : Prop :=
  ∀ (β : Type) [DecidableEq β] (f g : Store → β), sameStore f g = true ↔ f = g

def ExactDoubleStoreComparison : Prop :=
  ∀ (β : Type) [DecidableEq β] (f g : Store → Store → β), sameStore₂ f g = true ↔ f = g

def ExactStackStatementComparison : Prop :=
  ∀ q r : StackStatement, stackEq q r = true ↔ q = r

def ExactStackActionComparison : Prop :=
  ∀ (k : K') (a b : TM2to1.StAct K' StackAlphabet Store k), actionEq a b = true ↔ a = b

def ExactTapeLabelComparison : Prop :=
  ∀ q r : TapeLabel, labelEq q r = true ↔ q = r

end LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEqualityTargets
