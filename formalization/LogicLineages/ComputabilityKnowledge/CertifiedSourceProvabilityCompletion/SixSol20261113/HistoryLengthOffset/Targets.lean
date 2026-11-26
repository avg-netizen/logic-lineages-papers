module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.Targets
open GorbowPRProgram GorbowPRRegistry GorbowSyntax GorbowTheoryProof List.Vector

/-- Original checked certificate decoding and its empty-default branch are
retained in the all-vector calibration. Generic Nat-list calibration also
covers raw encoded histories; neither clause is reflected internally. -/
def NativeLength : Prop :=
  (∀ v : List.Vector Nat 1, evaluate lengthProgram v =
    ((GorbowNumericCertificate.decodeCertificate (v.get 0)).getD []).length) ∧
  (∀ xs : List Nat, evaluate lengthProgram (Encodable.encode xs ::ᵥ nil) = xs.length)

def InternalLengthNil : Prop := ∀ n (p : Program n) (ltag : Nat),
  (nodes p)[ltag]? = some ⟨1,lengthProgram⟩ → ∀ ctx,
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (lengthCall ltag (.zero : Term ctx)) .zero))

/-- Arbitrary symbolic head and tail codes, not only numeral/list images. -/
def InternalLengthCons : Prop := ∀ n (p : Program n) (ltag ctag : Nat),
  (nodes p)[ltag]? = some ⟨1,lengthProgram⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (head tail : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (lengthCall ltag (HistoryLookup.consCall ctag head tail)) (.succ (lengthCall ltag tail))))

/-- Actual Option-valued reference, including NONE and SOME zero. The offset
is true length, not encoded numerical size. No validity, successful-reference,
comparison, canonical-image, or native-calibration premise. -/
def InternalRightLookupOffset : Prop := ∀ n (p : Program n) (ltag atag rtag ctag : Nat),
  (nodes p)[ltag]? = some ⟨1,lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (left right index : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (rightOffset ltag atag rtag left right index))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.Targets
