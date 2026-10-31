module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecutionDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecutionTargets
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerFiniteTable PredictionCompilerFiniteExecution

def ExactReachableSimulation : Prop :=
  ∀ (c : Code) (k : Cont'),
    StateTransition.Respects (TM0.step postMachine) (tableStep (finiteData c k))
      (fun x d => x.q ∈ postLabels c k ∧ numericCfg c k x = d)

def ExactTermination : Prop :=
  ∀ (c : Code) (v : List Nat), (compiledEval c v).Dom ↔ (Code.eval c v).Dom

def ForwardEncodedOutput : Prop :=
  ∀ (c : Code) (v w : List Nat), w ∈ Code.eval c v →
    ∃ d, d ∈ compiledEval c v ∧ outputRelated c w d

def ReverseEncodedOutput : Prop :=
  ∀ (c : Code) (v : List Nat) d, d ∈ compiledEval c v →
    ∃ w, w ∈ Code.eval c v ∧ outputRelated c w d

end LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecutionTargets
