module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RankDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RankTargets
open PolynomialGraphCompletion

/-- Rank metadata agrees with the final literal SOURCE counter head. Arbitrary
interior words remain explicit prefixes; none is emitted as an ordinary row
term by this expansion. -/
def ActualResidualHeads : Prop := ∀ n c p, p ∈ residualWords n c →
  ∃ A : Word, p.2 = A ++ [counterLetter p.1 (c+p.1)]

/-- Every actual emitted residual atom, including its full original interior,
has its actual positive counter rank in the top-level source measure. -/
def ActualResidualTopRanks : Prop := ∀ n c p, p ∈ residualWords n c → ∀ A : Word,
  topRank (A++p.2) = p.1 ∧
  OuterShiftNormalization.coreWord (A++p.2) = A++p.2

/-- The source rank list is computed from ALL emitted row terms. There is no
negative preimage/interior term silently left outside the measure. -/
def ResidualRowRankBounds : Prop := ∀ D a i A n c, n+3 ≤ D →
  ∀ r ∈ rowRankList (counterResidualRow a i A n c), 3 ≤ r ∧ r ≤ D

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RankTargets
