module
public import LogicLineages.ModelsAlgebra.PGroups.QuotientExactLengthTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalExactLength
public import LogicLineages.ModelsAlgebra.PGroups.CoherentTerminal
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem quotient_exact_length : Targets.groupQuotientExactLength := by
  intro G _ p δ K T N hH hKT hN hbound hw
  have hK : K ≤ (transfiniteFiltration p δ : AddSubgroup G) := by rw [hH]; exact le_sup_left
  let i := AddSubgroup.inclusion hK
  have hi : Function.Injective i := by
    intro x y he
    have hval := congrArg (fun z : (transfiniteFiltration p δ : AddSubgroup G) => (z : G)) he
    exact Subtype.ext hval
  have hbK : ∀ x : K, p^N • x = 0 := by
    intro x
    apply hi
    simpa only [map_nsmul, map_zero] using hbound (i x)
  obtain ⟨w,hw⟩ := hw
  have hwH : p^(N-1) • i w ≠ 0 := by
    intro hz
    apply hw
    apply hi
    simpa only [map_nsmul, map_zero] using hz
  have hG := terminal_exact_length G p δ N hN hbound ⟨i w,hwH⟩
  obtain ⟨e,_⟩ := coherent_terminal_quotient G p δ K T hH hKT
  have hbQ : ∀ x : (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)), p^N • x = 0 := by
    intro x
    apply e.symm.injective
    simpa only [map_nsmul, map_zero] using hbK (e.symm x)
  have hwQ : p^(N-1) • e w ≠ 0 := by
    intro hz
    apply hw
    have hh := congrArg e.symm hz
    simpa only [map_nsmul, map_zero, e.symm_apply_apply] using hh
  have hQ := terminal_exact_length (G ⧸ T) p δ N hN hbQ ⟨e w,hwQ⟩
  exact ⟨⟨hG.1,hQ.1⟩, fun α hα => ⟨hG.2 α hα,hQ.2 α hα⟩⟩

end LogicLineages.ModelsAlgebra.PGroups
