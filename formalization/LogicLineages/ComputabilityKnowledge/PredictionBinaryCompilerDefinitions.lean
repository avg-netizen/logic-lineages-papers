module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachineDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogueDefinitions
@[expose] public section
/-! Actual rawbinary wrapper around the sequential-code TM0 compiler.
A supported source singleton result gives a literal raw output under the final
head. Numerical serialization/effectivity and full acceptability are separate. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryCompiler
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
inductive Label
  | prefix : Fin 4 → Label
  | body : PostLabel → Label
  | write
  | stop
instance : Inhabited Label := ⟨.prefix 0⟩

def machine (c : Code) : TM0.Machine TapeAlphabet Label := fun q a =>
  match q with
  | .prefix i =>
    if i.val = 0 then some (.prefix 1, .move .left)
    else if i.val = 1 then some (.prefix 2, .write (rawSymbol true))
    else if i.val = 2 then some (.prefix 3, .move .left)
    else some (.body (PredictionBinaryPrefixMachine.bodyStart c), .write bottomSymbol)
  | .body l => match postMachine l a with
    | some (l', op) => some (.body l', op)
    | none => some (.write, .move .right)
  | .write => some (.stop, .write (rawSymbol (workEq a (rawSymbol true))))
  | .stop => none

def embed (x : TM0.Cfg TapeAlphabet PostLabel) : TM0.Cfg TapeAlphabet Label :=
  ⟨.body x.q, x.Tape⟩

def initial (xs : List Bool) : TM0.Cfg TapeAlphabet Label := TM0.init (xs.map rawSymbol)

def final (b : Bool) : TM0.Cfg TapeAlphabet Label :=
  ⟨.stop, (PredictionBinaryOutputLayout.outputTape b).move .right |>.write (rawSymbol b)⟩

def states (c : Code) : List Label :=
  .write :: .stop :: (List.ofFn Label.prefix ++ (postLabels c Cont'.halt).map Label.body)

end LogicLineages.ComputabilityKnowledge.PredictionBinaryCompiler
