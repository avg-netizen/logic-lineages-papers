module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedValidityPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentationProof
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedPackedPresentation

theorem packedEncodingCalibration : NumberedPackedPresentationTargets.ActualPackedEncodingCalibration := by
  intro n arity Gamma q
  rfl

theorem packedDecodeNormalization : NumberedPackedPresentationTargets.ActualPackedDecodeNormalization := by
  intro n arity Gamma value
  cases h : decodePackedNumber n arity Gamma value with
  | none => simp [encdec, h]
  | some q =>
    have he := NumberedNumericDecodingProof.packedNumericSound n arity Gamma value q h
    unfold encdec
    rw [h]
    change Nat.succ (packedNumber q) = Nat.succ value
    exact congrArg Nat.succ he

theorem packedPresentationPrimitive : NumberedPackedPresentationTargets.ActualPackedPresentationPrimitive := by
  intro n arity Gamma
  have hs : Primrec (fun value => (decodePackedNumber n arity Gamma value).isSome) :=
    (NumberedTypedValidityPrimrecProof.numericPackedSuccessPrimitive n arity).comp
      ((Primrec.const Gamma).pair Primrec.id)
  have h : Primrec (fun value =>
      bif (decodePackedNumber n arity Gamma value).isSome then value + 1 else 0) :=
    Primrec.cond hs Primrec.succ (Primrec.const 0)
  exact Primrec.nat_iff.mp
    (h.of_eq (fun value => (packedDecodeNormalization n arity Gamma value).symm))

instance packedPrimcodable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primcodable (Packed (Fin n) arity Gamma) where
  toEncodable := packedEncodable n arity Gamma
  prim := packedPresentationPrimitive n arity Gamma

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentationProof
