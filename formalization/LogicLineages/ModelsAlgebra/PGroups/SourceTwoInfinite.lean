module
public import LogicLineages.ModelsAlgebra.PGroups.SourceTwoInfiniteTargets
public import LogicLineages.ModelsAlgebra.PGroups.TwoReservoirExtraction
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirObstruction
public import LogicLineages.ModelsAlgebra.PGroups.RawUpperBounds
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem source_two_infinite_no_difference_scott : Targets.groupSourceTwoInfiniteNoDifferenceScott := by
  intro p _ G _ _ N a b hab hN ha hb d hd hs
  obtain ⟨A,inst,hcount,hzero,⟨e⟩⟩ := two_reservoir_extraction p G N a b hab hN ha hb
  letI : AddCommGroup A := inst
  letI : Countable A := hcount
  have hz : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (a.val+1-1) : AddSubgroup A)) = 0 := by
    exact (congrArg (fun j : ℕ => Module.rank (ZMod p)
      (UlmLayer p (finiteFiltration p j : AddSubgroup A))) (Nat.add_sub_cancel a.val 1)).trans hzero
  exact reservoir_no_difference_two_scott p A (a.val+1) (b.val+1) (Nat.succ_pos _)
    (Nat.succ_lt_succ hab) hz d hd ((difference_scott_isomorphism 2 G _ e d hd).mp hs)

theorem raw_source_two_infinite_scott_bounds : Targets.groupRawSourceTwoInfiniteScottBounds := by
  intro p _ G _ _ N a b hab hN ha hb
  refine ⟨raw_bounded_pi_three_scott p G N hN, ?_⟩
  intro d hd hs
  exact source_two_infinite_no_difference_scott p G N a b hab hN ha hb d hd
    (raw_difference_scott_restriction G d hs)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
