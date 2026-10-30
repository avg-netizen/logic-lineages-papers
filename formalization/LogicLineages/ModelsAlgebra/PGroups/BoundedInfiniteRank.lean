module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedInfiniteRankTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlm
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem bounded_infinite_rank_exists : Targets.groupBoundedInfiniteRankExists := by
  classical
  intro p _ G _ _ _ N hN
  by_contra h
  have hf (j : ℕ) (hj : j < N) :
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0 :=
    lt_of_le_of_ne (countable_ulm_rank_bound p G j) (fun he => h ⟨⟨j,hj⟩,he⟩)
  letI : Finite (finiteFiltration p 0 : AddSubgroup G) :=
    finite_tail_from_ranks p G N hN 0 (Nat.zero_le N) (fun j _ hj => hf j hj)
  let f : G → (finiteFiltration p 0 : AddSubgroup G) := fun x => ⟨x,by trivial⟩
  have hi : Function.Injective f := by intro x y he; exact congrArg Subtype.val he
  letI : Finite G := Finite.of_injective f hi
  exact not_finite G

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
