module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCertificate
open Source Source.SourceMarkedSyntax
/-- Certificate uses a permutation-valued rank on the entire finite ranked signature. -/
def RankCertificate {n : Nat} (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n) : Prop :=
  Function.Injective rank ∧ ∀ f g, table f g = true ↔ (rank g).val < (rank f).val

instance rankCertificateDecidable {n : Nat} (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n) :
    Decidable (RankCertificate table rank) := by
  unfold RankCertificate Function.Injective
  infer_instance

def rankCertificateTest {n : Nat} (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n) : Bool :=
  decide (RankCertificate table rank)

def headRank {n : Nat} (rank : Fin n → Fin n) : Head (Fin n) → Nat
  | .ranked f => (rank f).val + 2
  | .application _ _ => 0
  | .zero | .succ | .cases _ | .recursor _ => 1
end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCertificate
