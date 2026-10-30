module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryExtensionCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryExtensionCode
open GorbowSyntax GorbowTheoryChecker GorbowTheoryProof GorbowSortedSyntaxCode
open LogicLineages.ComputabilityKnowledge.GorbowTheoryExtensionCode

def ExactProgram : Prop := ∀ axCheck (r raw : List Nat),
  extendProgram axCheck r raw=true ↔ axCheck raw=true ∨ raw=r

def ActualTheory : Prop := ∀ axCheck (R σ : Sentence),
  ProgramTheory (extendProgram axCheck (GorbowFormulaPrefixCode.encode R)) σ ↔
    GorbowClosedDeduction.extend (ProgramTheory axCheck) R σ

def CertificateDeduction : Prop := ∀ axCheck (R σ : Sentence),
  (∃ c, GorbowTheoryNumericCertificate.check (extendProgram axCheck (GorbowFormulaPrefixCode.encode R))
    0 (formulaCode σ) c=true) ↔
  (∃ c, GorbowTheoryNumericCertificate.check axCheck 0
    (GorbowSortedBooleanCode.binaryNumber 7 (formulaCode R) (formulaCode σ)) c=true)

def UniformExtension : Prop := ∀ axCheck, Primrec axCheck →
  Primrec (fun p : List Nat × List Nat => extendProgram axCheck p.1 p.2)

def Target : Prop := ExactProgram ∧ ActualTheory ∧ CertificateDeduction ∧ UniformExtension
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryExtensionCode
