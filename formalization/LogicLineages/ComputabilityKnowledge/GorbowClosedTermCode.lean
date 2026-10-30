module

public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificate
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

@[expose] public section

/-! Closed full-language and closed arithmetic term domains are distinct.
The token-5 test is calibrated only after closed-term validation; on open
terms token 5 can instead be a variable-index payload. Numeric list decoding
uses the same faithful list encoding as termNumber, without changing sorts. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowClosedTermCode

def arithmeticRaw (raw : List Nat) : Bool :=
  GorbowSyntaxValidation.validTerm 0 raw && raw.all (fun tag => decide (tag≠5))
def fullTermCode (code : Nat) : Bool :=
  match GorbowNumericCertificate.decodeFormula code with
  | none => false
  | some raw => GorbowSyntaxValidation.validTerm 0 raw
def arithmeticTermCode (code : Nat) : Bool :=
  match GorbowNumericCertificate.decodeFormula code with
  | none => false
  | some raw => arithmeticRaw raw
end LogicLineages.ComputabilityKnowledge.GorbowClosedTermCode
