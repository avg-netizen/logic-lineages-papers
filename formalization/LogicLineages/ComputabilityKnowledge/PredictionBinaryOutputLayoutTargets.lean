module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutTargets
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionBinarySentinel
open PredictionBinaryOutputLayout

def ExactHaltLayout : Prop :=
  ∀ (b : Bool) (x : TM1.Cfg TapeAlphabet TapeLabel Store),
    TM2to1.TrCfg (PartrecToTM2.halt [b.toNat]) x ↔ x = outputConfig b

def ExactOutputCell : Prop :=
  ∀ (b : Bool) (x : TM1.Cfg TapeAlphabet TapeLabel Store),
    TM2to1.TrCfg (PartrecToTM2.halt [b.toNat]) x →
      x.Tape.head = bottomSymbol ∧
      (x.Tape.move .right).head = if b then rawSymbol true else default

def ActualPostHalt : Prop :=
  ∀ (b : Bool) (x : TM1.Cfg TapeAlphabet TapeLabel Store),
    TM2to1.TrCfg (PartrecToTM2.halt [b.toNat]) x →
      TM0.step postMachine (TM1to0.trCfg tapeMachine x) = none

end LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutTargets
