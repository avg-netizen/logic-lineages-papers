module

public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeDefinitions
public import Mathlib.Computability.Partrec

/-! Paper 03 `prop:certificate`: explicit finite certificates and partial search.
Inputs and outputs have their standard list/product encodings. The certificate
contains the full canonical finite host universe, checked by literal equality;
the verifier recomputes the actual finite tests, not an oracle verdict.
Invalid forbidden-family inputs are rejected. This does not decide positive
JEP instances and does not invoke Carter's graph algorithm. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CertificateSearch
open FiniteCode

abbrev Input := List Code
abbrev Certificate := Code × Code × List Code

instance familyValidDecidable (U : Input) : Decidable (FamilyValid U) := by
  unfold FamilyValid
  infer_instance

def familyValidTest (U : Input) : Bool := decide (FamilyValid U)

def makeCertificate (c d : Code) : Certificate :=
  (c, d, hostCodes (c.1 + d.1))

def verify (U : Input) (t : Certificate) : Bool :=
  familyValidTest U && decide (t.2.2 = hostCodes (t.1.1 + t.2.1.1)) &&
    negativePairTest U t.1 t.2.1

/-- Every standard-coded pair is visited; malformed natural-number encodings
and nonnegative pair tests return `none`, not spurious certificates. -/
def atIndex (U : Input) (n : ℕ) : Option Certificate :=
  if familyValidTest U then
    (Encodable.decode n : Option (Code × Code)).bind fun p =>
      if negativePairTest U p.1 p.2 then some (makeCertificate p.1 p.2) else none
  else none

def search (U : Input) : Part Certificate := Nat.rfindOpt (atIndex U)

/-- Literal JEP for the actual finite order forests avoiding the given family. -/
def HasJEP (V : List FiniteOrderForest) : Prop :=
  ∀ F G : FiniteOrderForest,
    AvoidsForbidden V F.Carrier → AvoidsForbidden V G.Carrier →
    ∃ H : FiniteOrderForest, AvoidsForbidden V H.Carrier ∧
      Nonempty (F.Carrier ↪o H.Carrier) ∧ Nonempty (G.Carrier ↪o H.Carrier)

end LogicLineages.ModelsAlgebra.Forests.CertificateSearch
