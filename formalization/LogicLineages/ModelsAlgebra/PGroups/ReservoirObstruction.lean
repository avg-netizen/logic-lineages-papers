module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirObstructionTargets
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirChain
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirRank
public import LogicLineages.ModelsAlgebra.PGroups.StageReflection
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore
public import Mathlib.Data.Finsupp.Encodable
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u v

theorem reservoir_no_difference_two_scott : Targets.groupReservoirNoDifferenceTwoScott := by
  intro p _ A _ _ ell m hell hm hA
  let B := ZMod (p^ell)
  let C := ZMod (p^m)
  let j : B →+ C := powerCyclicInclusion p ell m (le_of_lt hm)
  have hj : Function.Injective j := power_cyclic_inclusion_injective p ell m (le_of_lt hm)
  exact chain_no_difference_two_scott (ReservoirGroup A B C) (reservoirStage A B C)
    (reservoir_monotone A B C) (reservoir_cover A B C)
    (reservoir_tuple_fixing A B C j hj)
    (reservoir_stage_nonisomorphism p A ell m hell hm hA)

theorem difference_scott_isomorphism : Targets.groupDifferenceScottIsomorphism.{u,v} := by
  intro α G H _ _ e d hd
  have transfer : ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B] (f : A ≃+ B),
      d.Realize (Fin.elim0 : Fin 0 → A) → d.Realize (Fin.elim0 : Fin 0 → B) := by
    intro A B _ _ f ht
    have hc : BackAndForth α (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → B) := by
      have he : (fun j : Fin 0 => f (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → B) := by funext j; exact Fin.elim0 j
      simpa only [he] using comparison_isomorphism α A B f 0 Fin.elim0
    have hr : BackAndForth α (Fin.elim0 : Fin 0 → B) (Fin.elim0 : Fin 0 → A) := by
      have he : (fun j : Fin 0 => f.symm (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → A) := by funext j; exact Fin.elim0 j
      simpa only [he] using comparison_isomorphism α B A f.symm 0 Fin.elim0
    exact ⟨(truth_transfer α B A 0 _ _ hr).2 d.sigmaPart hd.1 ht.1,
      (truth_transfer α A B 0 _ _ hc).1 d.piPart hd.2 ht.2⟩
  constructor
  · intro hs
    refine ⟨transfer G H e hs.1, ?_⟩
    intro K _ _ ht
    obtain ⟨f⟩ := hs.2 K ht
    exact ⟨e.symm.trans f⟩
  · intro hs
    refine ⟨transfer H G e.symm hs.1, ?_⟩
    intro K _ _ ht
    obtain ⟨f⟩ := hs.2 K ht
    exact ⟨e.trans f⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
