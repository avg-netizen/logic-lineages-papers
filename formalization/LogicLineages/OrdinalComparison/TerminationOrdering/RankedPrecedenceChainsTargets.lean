module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsTargets
open Source Source.SourceMarkedSyntax RankedPrecedenceCertificate

def ActualSymbolChainBound : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
  rankCertificateTest table rank = true → ∀ (length : Nat) (values : Nat → Fin n),
  (∀ i, i < length → table (values i) (values (i+1)) = true) →
  length + (rank (values length)).val ≤ (rank (values 0)).val ∧ length < n

def ActualHeadChainBound : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
  rankCertificateTest table rank = true → ∀ (length : Nat) (values : Nat → Head (Fin n)),
  (∀ i, i < length → RecursiveComparison.headAbove (NumberedCopyCertificate.tableAbove table) (values i) (values (i+1))) →
  length + headRank rank (values length) ≤ headRank rank (values 0) ∧ length ≤ n+1

def ActualHeadClassRank : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
  rankCertificateTest table rank = true → ∀ f g : Head (Fin n),
  RecursiveComparison.headEquivalent f g ↔ headRank rank f = headRank rank g

def ActualHeadPrecedenceCompatibility : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
  rankCertificateTest table rank = true → ∀ f f' g g' : Head (Fin n),
  RecursiveComparison.headEquivalent f f' → RecursiveComparison.headEquivalent g g' →
  (RecursiveComparison.headAbove (NumberedCopyCertificate.tableAbove table) f g ↔
    RecursiveComparison.headAbove (NumberedCopyCertificate.tableAbove table) f' g')

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsTargets
