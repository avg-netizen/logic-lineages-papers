module
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate
@[expose] public section
/-! External numeric proof-certificate constructors for the actual PA-plus-
explicit-axiom-program checker. Malformed numeric inputs decode to empty lists.
No DCB presentation, internal provability formula or derivability axiom is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperations
open GorbowProofChecker GorbowNumericCertificate GorbowSortedSyntaxCode

def mpLines (n : Nat) (raw : List Nat) (implication antecedent : List Line) : List Line :=
  implication ++ antecedent ++ [mpLine n raw antecedent.length 0]

def generalizeLines (n : Nat) (raw : List Nat) (premise : List Line) : List Line :=
  premise ++ [generalizeLine n raw 0]

def mpCertificate (n formula implication antecedent : Nat) : Nat :=
  certificateNumber (mpLines n ((decodeFormulaRaw formula).getD [])
    ((decodeCertificate implication).getD []) ((decodeCertificate antecedent).getD []))

def generalizeCertificate (n formula premise : Nat) : Nat :=
  certificateNumber (generalizeLines n ((decodeFormulaRaw formula).getD [])
    ((decodeCertificate premise).getD []))

end LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperations
