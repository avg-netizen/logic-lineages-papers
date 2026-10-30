module

public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmDimension
public import LogicLineages.ModelsAlgebra.PGroups.CountableBranches

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u v

private theorem append_empty {G : Type u} {n : ℕ} (a : Fin n → G) (d : Fin 0 → G) :
    append a d = a := by
  funext i
  simpa [append] using (Fin.addCases_left (m := n) (n := 0) (motive := fun _ => G)
    (left := a) (right := d) i)

theorem infinite_ulm_formula : Targets.groupInfiniteUlmFormula.{u,v} := by
  intro p _ j n
  constructor
  · exact countable_conj_all_complexity 3 (by simp) ℕ n (fun _ => 0)
      (fun m => ulmLowerFormula p j n m) (fun _ => 2)
      (fun _ => by exact_mod_cast (show (2 : ℕ) < 3 from by decide))
      (fun m => (ulm_lower_formula.{0,v} p j n m).1)
  · intro G _ a
    unfold infiniteUlmFormula
    rw [countable_conj_all_realization ℕ n _ _ G a, Cardinal.aleph0_le]
    constructor
    · intro h m
      apply (ulm_lower_rank_formula p j n m G a).mp
      simpa only [append_empty] using h m Fin.elim0
    · intro h m d
      have hm := (ulm_lower_rank_formula p j n m G a).mpr (h m)
      simpa only [append_empty] using hm

theorem countable_ulm_rank_bound : Targets.groupCountableUlmRankBound.{u} := by
  intro p _ G _ _ j
  letI : Countable (pSocle p (finiteFiltration p j : AddSubgroup G)) :=
    Subtype.val_injective.countable
  letI : Countable (UlmLayer p (finiteFiltration p j : AddSubgroup G)) :=
    (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p (finiteFiltration p j : AddSubgroup G))).countable
  exact (rank_le_card (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G))).trans
    Cardinal.mk_le_aleph0

theorem countable_infinite_ulm_formula : Targets.groupCountableInfiniteUlmFormula.{u} := by
  intro p _ G _ _ j n a
  rw [(infinite_ulm_formula.{u,0} p j n).2 G a]
  constructor
  · intro h
    exact le_antisymm (countable_ulm_rank_bound p G j) h
  · intro h
    exact h.ge

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
