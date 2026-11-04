module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetTargets
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedMultisetCertificate
open NumberedMultisetNumeric NumberedUniformPackedDecoding NumberedUniformMultiset

/-- All contexts and natural certificate codes, including every original rejection. -/
def ActualCertificateDecoderCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat),
    decodeRawCertificate n arity Gamma value =
      (decodeCertificate n arity Gamma value).map certificateData

/-- Uniformity is joint in the context and the numeric certificate. -/
def ActualUniformCertificateDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : List Ty × Nat => decodeRawCertificate n arity p.1 p.2)

/-- The unchanged original multiset test on all actual typed lists and certificates. -/
def ActualMultisetCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (source target : List (Packed (Fin n) arity Gamma))
    (certificate : MultisetCertificate n arity Gamma),
    rawMultisetTest (source.map packedCode) (target.map packedCode) (certificateData certificate) =
      multisetTest source target certificate

/-- Primitive recursion on the complete raw field product, without validity premises. -/
def ActualRawMultisetPrimitive : Prop :=
  ∀ n : Nat,
    Primrec (fun p : List (RawPacked n) × List (RawPacked n) × RawCertificate n =>
      rawMultisetTest p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetTargets
