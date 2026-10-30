module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDimensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormula
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDual

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

universe u v

theorem ulm_lower_rank_formula : Targets.groupUlmLowerRankFormula.{u} := by
  intro p _ j n m G _ a
  exact ((ulm_lower_formula.{u,0} p j n m).2 G a).trans Module.le_rank_iff.symm

theorem ulm_upper_rank_formula : Targets.groupUlmUpperRankFormula.{u,v} := by
  intro p _ j n m
  constructor
  · exact dual_complexity .sigma 2 n (ulmLowerFormula p j n (m + 1))
      (ulm_lower_formula.{u,v} p j n (m + 1)).1
  · intro G _ a
    unfold ulmUpperFormula
    rw [dual_realization G n (ulmLowerFormula p j n (m + 1)) a,
      ulm_lower_rank_formula p j n (m + 1) G a]
    rw [not_le, Nat.cast_add, Nat.cast_one]
    exact Cardinal.lt_natCast_add_one_iff

theorem ulm_exact_rank_formula : Targets.groupUlmExactRankFormula.{u,v} := by
  intro p _ j n m
  constructor
  · exact ⟨(ulm_lower_formula.{u,v} p j n m).1,
      (ulm_upper_rank_formula.{u,v} p j n m).1⟩
  · intro G _ a
    change ((ulmLowerFormula p j n m).Realize a ∧ (ulmUpperFormula p j n m).Realize a) ↔ _
    rw [ulm_lower_rank_formula p j n m G a, (ulm_upper_rank_formula.{u,v} p j n m).2 G a]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
