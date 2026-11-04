module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCertificateProof
open Source Source.SourceMarkedSyntax RankedPrecedenceCertificate

theorem actualRankCertificateTest : RankedPrecedenceCertificateTargets.ActualRankCertificateTest := by
  intro n table rank
  simp only [rankCertificateTest,decide_eq_true_eq]

theorem actualRankedStrictOrder : RankedPrecedenceCertificateTargets.ActualRankedStrictOrder := by
  intro n table rank h
  obtain ⟨hi,he⟩ := (actualRankCertificateTest n table rank).mp h
  refine ⟨?_,?_,?_⟩
  · intro f
    have hn : table f f ≠ true := fun ht => (Nat.lt_irrefl _) ((he f f).mp ht)
    cases hff : table f f <;> simp_all
  · intro f g k hfg hgk
    exact (he f k).mpr (Nat.lt_trans ((he g k).mp hgk) ((he f g).mp hfg))
  · intro f g hne
    have hv : (rank f).val ≠ (rank g).val := by
      intro hval
      exact hne (hi (Fin.ext hval))
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · exact Or.inr ((he g f).mpr hlt)
    · exact Or.inl ((he f g).mpr hgt)

theorem actualHeadRankCalibration : RankedPrecedenceCertificateTargets.ActualHeadRankCalibration := by
  intro n table rank h f g
  have he := ((actualRankCertificateTest n table rank).mp h).2
  cases f <;> cases g <;>
    simp [RecursiveComparison.headAbove,NumberedCopyCertificate.tableAbove,headRank,he]

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCertificateProof
