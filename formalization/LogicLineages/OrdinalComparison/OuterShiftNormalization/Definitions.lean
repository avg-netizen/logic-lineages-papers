module
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Definitions
public import LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.OuterShiftNormalization
open PolynomialGraphCompletion WordGuardCompletion

def ShiftOnly (w : Word) : Prop := ∀ a ∈ w, a.1 = 0

/-- Split off the maximal literal suffix of shifts, retaining every original
letter, including its unused fields, in exactly one of the two outputs. -/
def splitStep (a : Letter) (p : Word × Word) : Word × Word :=
  if p.1 = [] ∧ a.1 = 0 then ([],a::p.2) else (a::p.1,p.2)

def splitWord (w : Word) : Word × Word := w.foldr splitStep ([],[])
def coreWord (w : Word) : Word := (splitWord w).1
def shiftSuffix (w : Word) : Word := (splitWord w).2

def shiftSum (w : Word) : Int := w.foldr (fun a z => a.2.2.2+z) 0
def outerShift (w : Word) : Int := shiftSum (shiftSuffix w)
def normalizedWord (w : Word) : Word := coreWord w ++ [shiftLetter (outerShift w)]

def leafPairTail (A B : Word) : Nat := max (wordTail A) (wordTail B)
def nonlinearLeafTail (w B : Word) : Nat :=
  max (TerminalWordGrowthCompletion.terminalTail w (shiftSum B)) (wordTail B)

end LogicLineages.OrdinalComparison.OuterShiftNormalization
