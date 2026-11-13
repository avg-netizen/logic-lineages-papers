module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset
open GorbowPRProgram GorbowSyntax GorbowPRDefiningEquations List.Vector HistoryRuleSuffix

/-- Recursion-step inputs are [position,previousCount,code]. Add one exactly
when the actual repeated-tail suffix at position is nonempty. -/
def suffixAt : Program 3 := applyTwo HistoryLookup.drop (.projection 0) (.projection 2)
def countStep : Program 3 :=
  choose suffixAt (.projection 1) (applyOne .succ (.projection 1))
/-- Inputs [bound,code]. Counts nonempty actual suffixes below bound. -/
def count : Program 2 := .recursion (SixSol20261112.Fuel.zeroProgram 1) countStep
/-- The code is a sufficient bound, NOT the returned length. All ASTs explicit.
This standalone supplier is not claimed installed at the current SAME root. -/
def lengthProgram : Program 1 := .composition count (fun _ : Fin 2 => .projection 0)

def lengthCall {ctx : Nat} (tag : Nat) (code : Term ctx) : Term ctx := call tag (code ::ᵥ nil)
def rightOffset {ctx : Nat} (ltag atag rtag : Nat) (left right index : Term ctx) : Formula ctx :=
  .equal (HistoryLookup.lookupCall rtag (.add (lengthCall ltag left) index)
      (HistoryAppend.appendCall atag left right))
    (HistoryLookup.lookupCall rtag index right)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset
