module

public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificate
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNumericCertificate
open GorbowSyntax GorbowPACore GorbowProofChecker
open LogicLineages.ComputabilityKnowledge.GorbowNumericCertificate

def ExactDecoding : Prop :=
  (∀ code raw, decodeFormula code = some raw ↔ Encodable.encode raw = code) ∧
  (∀ code lines, decodeCertificate code = some lines ↔ certificateNumber lines = code)

def Calibration : Prop := ∀ n raw lines,
  check n (GorbowCodeConstructors.number raw) (certificateNumber lines) = verifies n raw lines

def ExactAcceptance : Prop := ∀ n f c,
  check n f c = true ↔ ∃ raw lines,
    f = GorbowCodeConstructors.number raw ∧ c = certificateNumber lines ∧ verifies n raw lines = true

def CoreProofEquivalence : Prop := ∀ n f,
  (∃ c, check n f c = true) ↔ ∃ φ : Formula n,
    f = GorbowCodeConstructors.formulaNumber φ ∧ Nonempty (Proof φ)

def UniformPrograms : Prop := Primrec decodeFormula ∧ Primrec decodeCertificate ∧
  Primrec certificateNumber ∧ Primrec (fun p : Nat × Nat × Nat => check p.1 p.2.1 p.2.2)

def Target : Prop := ExactDecoding ∧ Calibration ∧ ExactAcceptance ∧ CoreProofEquivalence ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNumericCertificate
