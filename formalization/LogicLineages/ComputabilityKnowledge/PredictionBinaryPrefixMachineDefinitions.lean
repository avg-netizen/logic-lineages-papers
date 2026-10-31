module
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelDefinitions
@[expose] public section
/-! Actual four-transition rawbinary prefix for the existing TM0 compiler.
The body is the real compiled machine, not a postulated partial function. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachine
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionBinarySentinel
inductive Label
  | prefix : Fin 4 → Label
  | body : PostLabel → Label

instance : Inhabited Label := ⟨.prefix 0⟩

def bodyStart (c : Code) : PostLabel :=
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  default

def machine (c : Code) : TM0.Machine TapeAlphabet Label := fun q a =>
  match q with
  | .prefix i =>
    if i.val = 0 then some (.prefix 1, .move .left)
    else if i.val = 1 then some (.prefix 2, .write (rawSymbol true))
    else if i.val = 2 then some (.prefix 3, .move .left)
    else some (.body (bodyStart c), .write bottomSymbol)
  | .body l => (postMachine l a).map (fun z => (.body z.1, z.2))

def embed (x : TM0.Cfg TapeAlphabet PostLabel) : TM0.Cfg TapeAlphabet Label :=
  ⟨.body x.q, x.Tape⟩

def initial (xs : List Bool) : TM0.Cfg TapeAlphabet Label := TM0.init (xs.map rawSymbol)

def advance (c : Code) : Nat → TM0.Cfg TapeAlphabet Label → Option (TM0.Cfg TapeAlphabet Label)
  | 0, x => some x
  | n + 1, x => (TM0.step (machine c) x).bind (advance c n)

end LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachine
