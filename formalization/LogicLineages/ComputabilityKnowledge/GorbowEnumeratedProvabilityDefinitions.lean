module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
public import Mathlib.Computability.PartrecCode

@[expose] public section
/-! Actual bounded axiom computation for a c.e. theory. Fuel is a logical
computation-certificate bound, never the source prediction game's runtime.
The fixed universal checker target must be proved genuinely uniform in the
ordinary program index and the fuel; pointwise Primrec existence is inadequate.
No particular source DCB axiom program or internal HB condition is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability
open GorbowSyntax GorbowTheoryProof GorbowPRProgram List.Vector

abbrev Code := Nat.Partrec.Code
abbrev Parameters := Code × Nat

def axiomCheck (p : Parameters) (raw : List Nat) : Bool :=
  decide (Nat.Partrec.Code.evaln p.2 p.1 (Encodable.encode raw) = some 1)

def boundedTheory (p : Parameters) : Sentence → Prop :=
  GorbowTheoryChecker.ProgramTheory (axiomCheck p)

def enumeratedTheory (c : Code) (sigma : Sentence) : Prop :=
  1 ∈ c.eval (Encodable.encode (GorbowFormulaPrefixCode.encode sigma))

def check (p : Parameters) (n formula certificate : Nat) : Bool :=
  GorbowTheoryNumericCertificate.check (axiomCheck p) n formula certificate

def arguments (c : Code) (fuel n formula certificate : Nat) : List.Vector Nat 5 :=
  Encodable.encode c ::ᵥ fuel ::ᵥ n ::ᵥ formula ::ᵥ certificate ::ᵥ List.Vector.nil

end LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability
