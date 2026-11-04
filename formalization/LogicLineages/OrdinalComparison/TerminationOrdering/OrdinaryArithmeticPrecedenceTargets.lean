module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticPrecedenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticPrecedenceTargets
open OrdinaryArithmetic OrdinaryArithmeticQuotient NumericPrecedenceCertificate RankedPrecedenceCertificate RankedPrecedenceCompleteness OrdinaryArithmeticPrecedence
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualArithmeticRankFormula : Prop := ∀ n, ∃ p : Program 2,
  (∀ v, evaluate p v = rankValue n v) ∧
  ∀ context certificate, (rankGraph p).Realize ![context,certificate] ↔
    ∃ (ctx : Context n) (rank : Fin n → Fin n),
      Encodable.decode context = some ctx ∧ decodeRank n certificate = some rank ∧ RankCertificate ctx.2 rank

def ActualArithmeticStrictContext : Prop := ∀ n, ∃ phi : Formula (Fin 1),
  ∀ context, phi.Realize ![context] ↔
    ∃ ctx : Context n, Encodable.decode context = some ctx ∧ StrictTotalTable ctx.2

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticPrecedenceTargets
