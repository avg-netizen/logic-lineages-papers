module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompletenessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompletenessTargets
open RankedPrecedenceCertificate RankedPrecedenceCompleteness

def ActualRankCertificateExistence : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool),
  (∃ rank : Fin n → Fin n, rankCertificateTest table rank = true) ↔ StrictTotalTable table

def ActualSymbolCycleExclusion : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool),
  StrictTotalTable table → ∀ (length : Nat) (values : Nat → Fin n), 0 < length →
  (∀ i, i < length → table (values i) (values (i+1)) = true) → values length ≠ values 0

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompletenessTargets
