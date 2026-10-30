module
public import LogicLineages.OrdinalComparison.CollectedRangeCellsTargets
public import LogicLineages.OrdinalComparison.CollectedRangeBandProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem collectedRangeCellTests : Targets.CollectedRangeCellTests := by
  intro c b tags hv hn x hx V hV
  dsimp only
  rcases collectedNonlinearRangeBand c b tags hv hn x hx with ⟨s,hY,hlo,hhi,homega⟩
  have hx2 : 2≤x := by
    have h4 : 4≤x := (le_max_left _ _).trans hx
    omega
  have hm := collectedMaximumPeak tags hv hn x hx2
  rcases hm.2.2.1 with ⟨rho,A,a,ha,hpeak⟩
  have hmax := hm.2.2.2
  rcases hV with ⟨k,rfl⟩
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro hlt
      have hks : k≤s := by
        by_contra h
        have hh := Phi_strictMono.monotone (show s+1≤k by omega)
        omega
      refine ⟨rho,A,a,ha,?_⟩
      rw [← hpeak,hY]
      exact Phi_strictMono.monotone hks
    · rintro ⟨sigma,B,b,hb,hlt⟩
      exact (hlt.trans (hmax sigma B b hb)).trans_lt hlo
  · constructor
    · intro hlt sigma B b hb
      exact (hmax sigma B b hb).trans_lt (hlo.trans hlt)
    · intro hall
      have hh := hall rho A a ha
      rw [← hpeak,hY] at hh
      have hsk : s<k := by
        by_contra h
        have hle := Phi_strictMono.monotone (show k≤s by omega)
        omega
      exact hhi.trans_le (Phi_strictMono.monotone (show s+1≤k from hsk))
  · intro heq
    by_cases hks : k≤s
    · have hle := Phi_strictMono.monotone hks
      rw [← hY,← heq] at hle
      omega
    · have hle := Phi_strictMono.monotone (show s+1≤k by omega)
      rw [← heq] at hle
      omega

end LogicLineages.OrdinalComparison
