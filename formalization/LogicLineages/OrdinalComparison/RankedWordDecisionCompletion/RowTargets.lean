module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RowDefinitions
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Targets
open PolynomialGraphCompletion CounterWordGuardCompletion

/-- Exact signed-shift extraction at every original admitted valuation.
Zero-weight occurrences and repeated raw names are preserved. -/
def ExactRowNormalization : Prop := ∀ D r ν,
  RowAllowed D r → RowDomain r ν →
  RowAllowed D (normalizeRow r) ∧ RowDomain (normalizeRow r) ν ∧
  RowValue (normalizeRow r) ν = RowValue r ν ∧
  rowVariables (normalizeRow r) = rowVariables r

/-- Literal generated counter heads remain in the original finite-degree
grammar. The list is nonempty, including the cubic bottom residual. -/
def ResidualWordSyntax : Prop := ∀ D n c, n+3 ≤ D →
  (residualWords n c).length = n+1 ∧
  ∀ p ∈ residualWords n c,
    3 ≤ p.1 ∧ p.1 ≤ n+3 ∧ WordAllowed D p.2

/-- The generated words denote the actual independently scheduled residual
counts, rather than an abstract value with a desired expansion equation. -/
def ResidualWordValues : Prop := ∀ n c t, leaderTail n c ≤ t →
  ((residualWords n c).map (fun p => wordValue p.2 t)).sum =
    (CounterLeaderExpansion.residuals n c t).sum

/-- A concrete whole-counter rewrite with all generated domains, source raw
name and interior word retained. This is a supporting source identity; it
does not assert ranked cancellation or a whole existential decision. -/
def ExactSourceCounterExpansion : Prop :=
  ∀ D a i A n c, n+3 ≤ D → WordAllowed D A → ∀ ν,
  expansionTail A n c ≤ ν i →
  RowAllowed D (counterExpansionRow a i A n c) ∧
  WordDomain (counterWord A n c) (ν i) ∧
  RowDomain (counterExpansionRow a i A n c) ν ∧
  2*a*(wordValue (counterWord A n c) (ν i) : Int) =
    RowValue (counterExpansionRow a i A n c) ν ∧
  ∀ j ∈ rowVariables (counterExpansionRow a i A n c), j = i

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Targets
