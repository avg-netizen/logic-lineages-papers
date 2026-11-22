module
public import LogicLineages.PermittedControl.OriginalGreatestGateGrowthTargets
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsOrbitProof
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsGrowthProof
import LogicLineages.PermittedControl.FixedHeadCollapseGraphSemanticProof
import LogicLineages.PermittedControl.CountProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalGreatestGateGrowth
open OrdinalComparison

theorem exactOrdinaryStrictGrowth : ExactOrdinaryStrictGrowth := by
  intro f B hf ρ rank F v nonlinear actual
  obtain ⟨q,hq,rfl⟩ := SelectedNonlinearImageBounds.ordinaryFullValueImage f B hf F (ρ rank) v
    nonlinear actual.1 actual.2
  have grows : q+1 ≤ f q := by
    simpa only [Function.iterate_one] using SelectedNonlinearImageBounds.orbitGrowth f B hf q 1
  exact hq.trans_lt (Nat.lt_of_succ_le grows)

theorem exactLimitCollapseStrictGrowth : ExactLimitCollapseStrictGrowth := by
  intro f B hf head x v hit
  obtain ⟨dom,value⟩ := ((FixedHeadCollapseGraph.sourceGraph f B hf (head,x)).1 v).mp hit
  let lam : NONote := ⟨rawNoteDecode head,dom.1⟩
  have complete := count_endpoint_facts f B hf lam.1.repr x (normalRepresentationSound lam) dom.2.1 dom.2.2
  have positive := complete.2.2.1
  have grows := SelectedNonlinearImageBounds.orbitGrowth f B hf x (completeCount f lam.1.repr x)
  rw [← complete.1] at grows
  change v = headCollapse f lam.1.repr x at value
  rw [value,complete.2.1]
  omega

end LogicLineages.PermittedControl.OriginalGreatestGateGrowth
