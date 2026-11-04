module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompletenessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificate
open OrdinaryArithmeticQuotient RankedPrecedenceCertificate
/-- Freeze the actual dependent finite-function encoding, distinct from Primcodable.finArrow. -/
def rankEncoding (n : Nat) : Encodable (Fin n → Fin n) :=
  @Encodable.finPi n (fun _ => Fin n) (fun _ => inferInstance)

def decodeRank (n : Nat) : Nat → Option (Fin n → Fin n) := @Encodable.decode _ (rankEncoding n)

def numericRankTest (n : Nat) (context certificate : Nat) : Bool :=
  (Encodable.decode (α := Context n) context).any (fun ctx =>
    (decodeRank n certificate).any (fun rank => rankCertificateTest ctx.2 rank))
end LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificate
