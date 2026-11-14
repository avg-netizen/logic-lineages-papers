module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.EncodingProof
open Source NumberedLeastCodeRepresentative NumberedTypeCodecPrimrec
open OrdinaryArithmeticQuotientDecoderProof NumberedMultisetNumeric

theorem finEncoding (n : Nat) (s : Fin n) : Encodable.encode s = s.val := rfl

theorem typeCanonical : Canonical Ty inferInstance := by
  intro k tau h
  change some (typeEquiv.symm k) = some tau at h
  have ht := Option.some.inj h
  change typeNumber tau = k
  rw [← ht]
  exact typeEquiv.apply_symm_apply k

theorem windowComponents (n raw : Nat) (window : ExchangeNumericSuppliers.Window n)
    (h : Encodable.decode raw = some window) :
    (Nat.unpair raw).1 = numbersNumber (window.1.map Fin.val) ∧
    (Nat.unpair raw).2 = numbersNumber (window.2.map typeNumber) := by
  rw [Encodable.decode_prod_val] at h
  cases hs : Encodable.decode (α := List (Fin n)) (Nat.unpair raw).1 with
  | none => simp only [hs,Option.bind_none] at h; cases h
  | some symbols =>
    cases ht : Encodable.decode (α := List Ty) (Nat.unpair raw).2 with
    | none => simp only [hs,ht,Option.bind_some,Option.map_none] at h; cases h
    | some types =>
      simp only [hs,ht,Option.bind_some,Option.map_some,Option.some.injEq] at h
      cases h
      have heS := canonicalList (Fin.encodable n) (canonicalFin n) _ symbols hs
      have heT := canonicalList (inferInstance : Encodable Ty) typeCanonical _ types ht
      rw [OriginalArgumentPermutation.NativeProof.listEncoding] at heS heT
      constructor
      · simpa only [finEncoding] using heS.symm
      · exact heT.symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.EncodingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.EncodingProof
