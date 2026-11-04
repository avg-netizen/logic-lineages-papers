module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificatesDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates.Targets
open GorbowSyntax GorbowTheoryProof

def LiteralBeta : Prop := ∀ a b i r, closedBeta a b i r = literalBeta a b i r

/-- Actual internal PA proof of each correct concrete beta entry. The numeric
remainder equality is discharged by the final finite-sequence witness gate. -/
def PositiveBetaCertificates : Prop := ∀ (T : Sentence → Prop) (a b i r : Nat),
  a % ((i+1)*b+1) = r → Nonempty (Derivation T (closedBeta a b i r))

/-- Pointwise internal existence for every concrete code/index triple, not an
unproved internal universal division/totality theorem. -/
def PointwiseValueTotality : Prop := ∀ (T : Sentence → Prop) (a b i : Nat),
  Nonempty (Derivation T
    (GorbowArithmeticCompositionCertificates.encodedExists (valueBody a b i)))

/-- ALL supplied finite sequences acquire actual arithmetic beta certificates.
This does not assert a still-unpaid internally guarded universal sequence. -/
def FiniteSequenceCertificates : Prop := ∀ (T : Sentence → Prop) (n : Nat)
    (values : List.Vector Nat n), ∃ a b : Nat, ∀ i : Fin n,
  Nonempty (Derivation T (closedBeta a b i.val (values.get i)))

def Target : Prop := LiteralBeta ∧ PositiveBetaCertificates ∧
  PointwiseValueTotality ∧ FiniteSequenceCertificates
end LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates.Targets
