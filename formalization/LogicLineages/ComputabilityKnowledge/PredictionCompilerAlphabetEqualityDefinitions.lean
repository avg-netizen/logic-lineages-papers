module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportDefinitions
@[expose] public section
/-! Explicit complete alphabet and finite input-domain comparison for the
actual four-stack TM2-to-TM1 compiler. No function-space evaluation is used:
the list is the symbolic finite product of four five-value slots and one bit. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEquality
open Turing Turing.PartrecToTM2 PredictionCompilerSupport PredictionCompilerTapeSupport

def slots (m r a s : Store) : K' → Store
  | .main => m
  | .rev => r
  | .aux => a
  | .stack => s

def workSymbols : List TapeAlphabet :=
  [false, true].flatMap (fun b => symbols.flatMap (fun m => symbols.flatMap (fun r =>
    symbols.flatMap (fun a => symbols.map (fun s => (b, slots m r a s))))))

def workEq (a b : TapeAlphabet) : Bool :=
  decide (a.1 = b.1) && decide (a.2 .main = b.2 .main) &&
    decide (a.2 .rev = b.2 .rev) && decide (a.2 .aux = b.2 .aux) &&
    decide (a.2 .stack = b.2 .stack)

def sameInputs {β : Type} (compare : β → β → Bool)
    (f g : TapeAlphabet → Store → β) : Bool :=
  workSymbols.all (fun a => symbols.all (fun s => compare (f a s) (g a s)))

end LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEquality
