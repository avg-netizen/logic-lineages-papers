module

public import LogicLineages.ComputabilityKnowledge.GorbowContextTransport
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation

@[expose] public section

/-! A conservative parser ambient obtained from all raw tokens, not a free
variable count. Existing raw/numeric term and formula encodings are unchanged. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRawContextBound

def rawBound (raw : List Nat) : Nat := raw.foldl max 0 + 1
def validAnyTerm (raw : List Nat) : Bool := GorbowSyntaxValidation.validTerm (rawBound raw) raw
def validAnyFormula (raw : List Nat) : Bool := GorbowSyntaxValidation.validFormula (rawBound raw) raw
end LogicLineages.ComputabilityKnowledge.GorbowRawContextBound
