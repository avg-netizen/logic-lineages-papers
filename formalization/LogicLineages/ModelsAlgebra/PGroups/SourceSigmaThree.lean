module
public import LogicLineages.ModelsAlgebra.PGroups.SourceSigmaThreeTargets
public import LogicLineages.ModelsAlgebra.PGroups.SigmaThreeReflection
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirObstruction
public import LogicLineages.ModelsAlgebra.PGroups.TwoReservoirExtraction
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem sigma_scott_isomorphism : Targets.groupSigmaScottIsomorphism.{u,v} := by
  intro α G H _ _ e φ hφ
  have transfer : ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B]
      (f : A ≃+ B), φ.Realize (Fin.elim0 : Fin 0 → A) →
      φ.Realize (Fin.elim0 : Fin 0 → B) := by
    intro A B _ _ f ht
    have he : (fun j : Fin 0 => f.symm (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → A) := by
      funext j
      exact Fin.elim0 j
    have hc := GroupBackAndForth.comparison_isomorphism α B A f.symm 0 Fin.elim0
    rw [he] at hc
    exact (truth_transfer α B A 0 Fin.elim0 _ hc).2 φ hφ ht
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

theorem reservoir_no_sigma_three_scott : Targets.groupReservoirNoSigmaThreeScott := by
  intro p _ A _ _ ell m hell hm hA
  let B := ZMod (p^ell)
  let C := ZMod (p^m)
  let j : B →+ C := powerCyclicInclusion p ell m (le_of_lt hm)
  have hj : Function.Injective j := power_cyclic_inclusion_injective p ell m (le_of_lt hm)
  exact chain_no_sigma_three_scott (ReservoirGroup A B C) (reservoirStage A B C)
    (reservoir_monotone A B C) (reservoir_cover A B C)
    (reservoir_tuple_fixing A B C j hj)
    (reservoir_stage_nonisomorphism p A ell m hell hm hA)

theorem raw_source_two_infinite_no_sigma_three : Targets.groupRawSourceTwoInfiniteNoSigmaThree := by
  intro p _ G _ _ N a b hab hN ha hb φ hφ hs
  obtain ⟨A,inst,hcount,hzero,⟨e⟩⟩ := two_reservoir_extraction p G N a b hab hN ha hb
  letI : AddCommGroup A := inst
  letI : Countable A := hcount
  have hz : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (a.val+1-1) : AddSubgroup A)) = 0 :=
    (congrArg (fun j : ℕ => Module.rank (ZMod p)
      (UlmLayer p (finiteFiltration p j : AddSubgroup A))) (Nat.add_sub_cancel a.val 1)).trans hzero
  exact reservoir_no_sigma_three_scott p A (a.val+1) (b.val+1) (Nat.succ_pos _)
    (Nat.succ_lt_succ hab) hz φ hφ ((sigma_scott_isomorphism 3 G _ e φ hφ).mp
      (raw_scott_restriction G φ hs))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
