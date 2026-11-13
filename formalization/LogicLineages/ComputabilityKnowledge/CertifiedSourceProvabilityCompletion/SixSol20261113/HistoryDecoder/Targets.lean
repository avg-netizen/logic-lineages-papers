module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

/-- Native all-vector calibration is checked separately, never reflected into PA. -/
def NativeLeft : Prop := ∀ v : List.Vector Nat 1,
  evaluate (decoder false) v = (Nat.unpair v.head).1
def NativeRight : Prop := ∀ v : List.Vector Nat 1,
  evaluate (decoder true) v = (Nat.unpair v.head).2

def LeftPairInstalled : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨1,decoder false⟩ →
    (nodes p)[pairTag false tag]? = some ⟨2,HistoryCodec.pair⟩
def RightPairInstalled : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨1,decoder true⟩ →
    (nodes p)[pairTag true tag]? = some ⟨2,HistoryCodec.pair⟩

/-- Actual internal inverse on the actual pair child of this decoder.
No native-evaluation reflection, abstract PR correctness, decoder or loop oracle. -/
def InternalLeftInverse : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨1,decoder false⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (GorbowPRDefiningEquations.call tag
      (GorbowPRDefiningEquations.call (pairTag false tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil)) a))
def InternalRightInverse : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨1,decoder true⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (GorbowPRDefiningEquations.call tag
      (GorbowPRDefiningEquations.call (pairTag true tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil)) b))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.Targets
