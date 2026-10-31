module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatingMachineDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionAttachExitDefinitions
@[expose] public section
/-! Actual source TM0 plus validating exit. The bridge is a real self-write.
There is NO sentinel prefix here: entry receives the complete prepared stack
tape for [sentinel(xs),e]. Program entry is explicit, not the global default. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatedBody
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
inductive Label
  | source : PostLabel → Label
  | validate : PredictionValidatingMachine.Label → Label
instance : Inhabited Label := ⟨.validate .check⟩

def machine : TM0.Machine TapeAlphabet Label := fun q a =>
  match q with
  | .source l => match postMachine l a with
    | some (l', op) => some (.source l', op)
    | none => some (.validate .check, .write a)
  | .validate v => (PredictionValidatingMachine.machine v a).map (fun z => (.validate z.1, z.2))

def sourceCfg (x : TM0.Cfg TapeAlphabet PostLabel) : TM0.Cfg TapeAlphabet Label := ⟨.source x.q, x.Tape⟩

def validatorCfg (x : TM0.Cfg TapeAlphabet PredictionValidatingMachine.Label) : TM0.Cfg TapeAlphabet Label :=
  ⟨.validate x.q, x.Tape⟩

def flatten : TM0.Cfg TapeAlphabet PostLabel ⊕ TM0.Cfg TapeAlphabet PredictionValidatingMachine.Label →
    TM0.Cfg TapeAlphabet Label
  | .inl x => sourceCfg x
  | .inr x => validatorCfg x

def initial (c : Code) (v : List Nat) : TM0.Cfg TapeAlphabet Label :=
  sourceCfg (PredictionCompilerFiniteExecution.sourceInit c v)

def readout (x : TM0.Cfg TapeAlphabet Label) : Bool := workEq x.Tape.head (rawSymbol true)

def validatorLabels : List PredictionValidatingMachine.Label := [.check, .first, .second, .stop, .loop]

def states (c : Code) : List Label :=
  validatorLabels.map Label.validate ++ (postLabels c Cont'.halt).map Label.source

end LogicLineages.ComputabilityKnowledge.PredictionValidatedBody
