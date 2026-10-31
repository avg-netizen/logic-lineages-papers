module
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceSpectrumCompleteTargets
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorDifferenceProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedDifferenceIndexProof
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScott
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryFiniteGenerationProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
private theorem attained_successor (p:ℕ) [Fact p.Prime] (α:Ordinal.{0})
    (h:AttainedReducedDifference p α) : ∃β:Ordinal.{0},α=β+1 := by
  obtain ⟨G,inst,hc,hG,hr,he⟩ := h
  letI := inst
  letI : Countable G := hc
  rcases Ordinal.zero_or_succ_or_isSuccLimit α with hz|⟨β,hβ⟩|hα
  · subst α
    obtain ⟨d,hd,hs⟩ := he.1
    exact (raw_no_zero_difference_scott G d hd hs).elim
  · exact ⟨β,by simpa only [Order.succ_eq_add_one] using hβ.symm⟩
  · exact (reduced_no_limit_difference_index G p hG hr α hα he).elim
private theorem infinite_no_one (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G]
    [Countable G] [Infinite G] (hG:∀x:G,∃k:ℕ,p^k • x=0) :
    ¬RawDifferenceEndpoint G 1 := by
  intro h
  obtain ⟨d,hd,hs⟩ := h.1
  have hLF : LocallyFinite G := by
    intro n a
    letI := p_primary_finite_tuple_closure G p (Fact.out : p.Prime).ne_zero hG n a
    exact Set.toFinite _
  exact locally_finite_no_difference_one_scott G hLF d hd (raw_difference_scott_restriction G d hs)

theorem difference_spectrum_full_source : Targets.differenceSpectrumFullSource := by
  intro p _ α _
  refine ⟨⟨attained_successor p α,?_⟩,⟨?_,?_⟩⟩
  · rintro ⟨β,hβ⟩
    subst α
    obtain ⟨G,inst,hc,hG,hr,he,_⟩ := successor_difference_realization p β inferInstance
    exact ⟨G,inst,hc,hG,hr,he⟩
  · rintro ⟨G,inst,hc,hi,hG,hr,he⟩
    letI := inst
    letI : Countable G := hc
    letI : Infinite G := hi
    have hs := attained_successor p α ⟨G,inst,hc,hG,hr,he⟩
    refine ⟨?_,hs⟩
    by_contra hn
    have hlt:α<2 := lt_of_not_ge hn
    have hle:α≤1 := Order.lt_two_iff.mp hlt
    obtain ⟨β,hβ⟩ := hs
    have hpos:0<α := by rw [hβ]; positivity
    have hone:α=1 := le_antisymm hle (Order.one_le_iff_ne_zero.mpr hpos.ne')
    rw [hone] at he
    exact infinite_no_one p G hG he
  · rintro ⟨hlarge,β,hβ⟩
    subst α
    obtain ⟨G,inst,hc,hG,hr,he,hi⟩ := successor_difference_realization p β inferInstance
    exact ⟨G,inst,hc,hi hlarge,hG,hr,he⟩
end LogicLineages.ModelsAlgebra.PGroups
