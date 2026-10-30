module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryNumericCertificate
open GorbowSyntax GorbowTheoryProof GorbowTheoryChecker GorbowSortedSyntaxCode
open LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate

def Calibration : Prop := ∀ axCheck n raw lines,
  check axCheck n (formulaRawNumber raw) (GorbowNumericCertificate.certificateNumber lines)=
    verifies axCheck n raw lines

def ExactAcceptance : Prop := ∀ axCheck n f c,
  check axCheck n f c=true ↔ ∃ raw lines,
    f=formulaRawNumber raw ∧ c=GorbowNumericCertificate.certificateNumber lines ∧ verifies axCheck n raw lines=true

def ProofEquivalence : Prop := ∀ axCheck n f,
  (∃ c, check axCheck n f c=true) ↔ ∃ φ : Formula n,
    f=formulaCode φ ∧ Nonempty (Derivation (ProgramTheory axCheck) φ)

def MalformedRejection : Prop :=
  (∀ axCheck n f c, decodeFormulaRaw f=none ∨ GorbowNumericCertificate.decodeCertificate c=none → check axCheck n f c=false) ∧
  (∀ axCheck n f c raw, decodeFormulaRaw f=some raw → GorbowSyntaxValidation.validFormula n raw=false → check axCheck n f c=false)

def UniformProgram : Prop := ∀ axCheck, Primrec axCheck →
  Primrec (fun p : Nat × Nat × Nat => check axCheck p.1 p.2.1 p.2.2)

def Target : Prop := Calibration ∧ ExactAcceptance ∧ ProofEquivalence ∧ MalformedRejection ∧ UniformProgram
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryNumericCertificate
