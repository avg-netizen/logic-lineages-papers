module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCertificateTargets
open Source Source.SourceMarkedSyntax RankedPrecedenceCertificate

def ActualRankCertificateTest : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
  rankCertificateTest table rank = true ↔ RankCertificate table rank

def ActualRankedStrictOrder : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
  rankCertificateTest table rank = true →
  (∀ f, table f f = false) ∧
  (∀ f g h, table f g = true → table g h = true → table f h = true) ∧
  (∀ f g, f ≠ g → table f g = true ∨ table g f = true)

def ActualHeadRankCalibration : Prop := ∀ (n : Nat) (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
  rankCertificateTest table rank = true → ∀ f g : Head (Fin n),
  (RecursiveComparison.headAbove (NumberedCopyCertificate.tableAbove table) f g ↔ headRank rank g < headRank rank f)

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCertificateTargets
