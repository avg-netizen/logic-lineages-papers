module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.BoundedCategoricity
public import LogicLineages.ModelsAlgebra.PGroups.BoundedUlmTable
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlm
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
public import Mathlib.SetTheory.Cardinal.ToNat
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem countable_ulm_table_exists : Targets.groupCountableUlmTableExists := by
  classical
  intro p _ G _ _ N
  have he : ∀ j : Fin N, ∃ entry : Option ℕ,
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup G)) =
        (match entry with | none => Cardinal.aleph0 | some m => (m : Cardinal)) := by
    intro j
    let r := Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup G))
    by_cases h : r = Cardinal.aleph0
    · exact ⟨none,h⟩
    · exact ⟨some r.toNat, (Cardinal.cast_toNat_of_lt_aleph0
        (lt_of_le_of_ne (countable_ulm_rank_bound p G j.val) h)).symm⟩
  choose entries he using he
  exact ⟨entries,he⟩

theorem bounded_pi_three_scott : Targets.groupBoundedPiThreeScott := by
  intro p _ G _ _ N hb
  obtain ⟨entries,he⟩ := countable_ulm_table_exists p G N
  refine ⟨entries,(bounded_ulm_table.{0,0} p N entries).1, ?_⟩
  have hbot : finiteFiltration p N = (⊥ : AddSubgroup G) := by
    apply le_antisymm _ bot_le
    intro g hg
    obtain ⟨x,rfl⟩ := (finite_filtration_multiple_image G p N).le hg
    exact hb x
  constructor
  · exact ((bounded_ulm_table.{0,0} p N entries).2 G).mpr ⟨hbot,he⟩
  · intro H _ _ hH
    obtain ⟨hbotH,heH⟩ := ((bounded_ulm_table.{0,0} p N entries).2 H).mp hH
    apply bounded_ulm_categoricity p G H N hb
    · intro h
      have hm : p ^ N • h ∈ (finiteFiltration p N : AddSubgroup H) :=
        (finite_filtration_multiple_image H p N).ge ⟨h,rfl⟩
      rw [hbotH] at hm
      exact hm
    · intro j
      exact (he j).trans (heH j).symm

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
