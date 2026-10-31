module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogueDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogueTargets
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionBinarySentinel PredictionBinaryEpilogue

def ExactThreeFuel : Prop :=
  ∀ (b : Bool) (x : TM1.Cfg TapeAlphabet TapeLabel Store),
    TM2to1.TrCfg (PartrecToTM2.halt [b.toNat]) x → run 3 (initial x) = some (final b x)

def NoEarlyReturn : Prop :=
  ∀ (x : TM1.Cfg TapeAlphabet TapeLabel Store), run 2 (initial x) = none

def ExactFinalOutput : Prop :=
  ∀ (b : Bool) (x : TM1.Cfg TapeAlphabet TapeLabel Store),
    (final b x).Tape.head = rawSymbol b ∧ TM0.step machine (final b x) = none

end LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogueTargets
