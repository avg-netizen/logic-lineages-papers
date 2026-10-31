module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluationDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluation.Targets
open Turing PredictionFiniteAlphabet

def EvaluationTransport : Prop := ∀ (p : Table) (c : Raw),
  StateTransition.eval (TM0.step (machine p)) (toCfg p c) =
    toCfg p <$> StateTransition.eval (step p) c

/-- Bounded simulation includes one unit for observing termination, as in
ExactBoundedSimulation's strict `n < fuel` convention. -/
def BoundedEvaluation : Prop := ∀ (p : Table) (c : Raw) (y : Cfg p),
  (∃ fuel d, bounded p fuel c = some d ∧ toCfg p d = y) ↔
    y ∈ StateTransition.eval (TM0.step (machine p)) (toCfg p c)

def HeadModulo : Prop := ∀ (p : Table) (c : Raw), (toCfg p c).Tape.head.val = rawHead p c

def BinaryOutputEvaluation : Prop := ∀ (code : Nat) (xs : List Bool) (b : Bool),
  (∃ fuel d, simulate code fuel xs = some d ∧
    d.2.1 % width (decodeTable code) = inputSymbol b) ↔
  ∃ y, y ∈ StateTransition.eval (TM0.step (machine (decodeTable code)))
      (toCfg (decodeTable code) (initial (decodeTable code) xs)) ∧
    y.Tape.head.val = inputSymbol b
end LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluation.Targets
