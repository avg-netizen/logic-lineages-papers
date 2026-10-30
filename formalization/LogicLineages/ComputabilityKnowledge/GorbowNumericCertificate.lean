module

public import LogicLineages.ComputabilityKnowledge.GorbowProofChecker

@[expose] public section

/-! External numeric certificates for the concrete PA core. This is not an
arithmetical formula representing Pr_D, nor an internal derivability theorem.
The exact chosen Encodable representation is checked in both numeric inputs. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNumericCertificate
open GorbowProofChecker

def decodeFormula (code : Nat) : Option (List Nat) := do
  let raw ← Encodable.decode (α := List Nat) code
  if Encodable.encode raw = code then some raw else none

def decodeCertificate (code : Nat) : Option (List Line) := do
  let lines ← Encodable.decode (α := List Line) code
  if Encodable.encode lines = code then some lines else none

def certificateNumber (lines : List Line) : Nat := Encodable.encode lines

def check (n formula certificate : Nat) : Bool :=
  match decodeFormula formula, decodeCertificate certificate with
  | some raw,some lines => verifies n raw lines
  | _,_ => false
end LogicLineages.ComputabilityKnowledge.GorbowNumericCertificate
