module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificateTargets
open OrdinaryArithmeticQuotient RankedPrecedenceCertificate RankedPrecedenceCompleteness NumericPrecedenceCertificate

def ActualNumericRankCalibration : Prop := ∀ n context certificate,
  numericRankTest n context certificate = true ↔
    ∃ (ctx : Context n) (rank : Fin n → Fin n),
      Encodable.decode context = some ctx ∧ decodeRank n certificate = some rank ∧ RankCertificate ctx.2 rank

def ActualNumericRankPrimitive : Prop := ∀ n, Primrec₂ (numericRankTest n)

def ActualNumericRankExistence : Prop := ∀ n context,
  (∃ certificate, numericRankTest n context certificate = true) ↔
    ∃ ctx : Context n, Encodable.decode context = some ctx ∧ StrictTotalTable ctx.2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificateTargets
