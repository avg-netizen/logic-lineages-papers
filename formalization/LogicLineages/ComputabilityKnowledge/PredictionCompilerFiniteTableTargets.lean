module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTableDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTableTargets
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionCompilerFiniteTable

def ExactActionAssembly : Prop :=
  ∀ (c : Code) (k : Cont'), PredictionFiniteSerialization.finiteMachine (finiteData c k) = finitePost c k

def ExactTableCode : Prop :=
  ∀ (c : Code) (k : Cont'), PredictionFiniteAlphabet.decodeTable (numericCode c k) = numericTable c k

def ExactFiniteStep : Prop :=
  ∀ (c : Code) (k : Cont') (x : TM0.Cfg TapeAlphabet PostLabel),
    x.q ∈ postLabels c k →
    (TM0.step postMachine x).map (finiteCfg c k) = TM0.step (finitePost c k) (finiteCfg c k x)

/-- Polymorphic statement avoids reducing the closed 1,250-symbol list during elaboration. -/
def NumericStepAt {q a : Nat} (m : PredictionFiniteSerialization.FinMachine q a)
    (x : TM0.Cfg (Fin (a + 3)) (Fin (q + 1)))
    (next : Option (TM0.Cfg (Fin (a + 3)) (Fin (q + 1)))) : Prop :=
  TM0.step (PredictionFiniteAlphabet.machine (PredictionFiniteSerialization.table 0 m))
    (PredictionFiniteSerialization.embedCfg x) = next.map PredictionFiniteSerialization.embedCfg

def ExactNumericStep : Prop :=
  ∀ (c : Code) (k : Cont') (x : TM0.Cfg TapeAlphabet PostLabel),
    x.q ∈ postLabels c k →
    NumericStepAt (finiteData c k) (finiteCfg c k x)
      ((TM0.step postMachine x).map (finiteCfg c k))

end LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTableTargets
