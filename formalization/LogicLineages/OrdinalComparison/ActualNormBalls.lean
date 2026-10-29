module
public import LogicLineages.OrdinalComparison.ActualNormBallTargets
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualNormBallDenotationMembership : Targets.ActualNormBallDenotationMembership := by
  classical
  intro b a
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
    refine ⟨normalRepresentationSound n, ?_⟩
    rw [actualOrdinalNorm_notationCorrespondence n]
    exact (notationNormBall_exact b n).mp hn
  · rintro ⟨ha, hn⟩
    obtain ⟨n, he⟩ := normalRepresentationComplete a ha
    refine Finset.mem_image.mpr ⟨n, (notationNormBall_exact b n).mpr ?_, he⟩
    rw [← actualOrdinalNorm_notationCorrespondence n, he]
    exact hn

theorem actualFiniteNormBalls : Targets.ActualFiniteNormBalls := by
  classical
  intro b
  have heq : {a : Ordinal.{0} | a < epsilonZero ∧ actualOrdinalNorm a ≤ b} =
      ↑((notationNormBall b).image (fun n => n.1.repr)) := by
    ext a
    exact (actualNormBallDenotationMembership b a).symm
  rw [heq]
  exact Finset.finite_toSet _

end LogicLineages.OrdinalComparison
