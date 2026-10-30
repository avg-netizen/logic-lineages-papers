module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryChecker
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode

@[expose] public section
/-! External numeric proof certificates for an explicit axiom program. Formula
inputs use the paid sorted syntax code; certificate numbers use the separately
specified faithful List Line codec. No cross-sort/global gc claim about proof
certificates, arithmetic formula Pr, or representability is made here. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate

def check (axCheck : List Nat → Bool) (n formula certificate : Nat) : Bool :=
  match GorbowSortedSyntaxCode.decodeFormulaRaw formula, GorbowNumericCertificate.decodeCertificate certificate with
  | some raw,some lines => GorbowTheoryChecker.verifies axCheck n raw lines
  | _,_ => false
end LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate
