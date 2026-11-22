module
public import LogicLineages.PermittedControl.ActualZeroClassOutputStateTargets
import LogicLineages.PermittedControl.ActualZeroClassOutputStateRankProof
import LogicLineages.PermittedControl.ActualZeroClassConcreteChargeProof
import LogicLineages.PermittedControl.ActualZeroClassValueConservationProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassOutputState
open scoped Classical
open ActualZeroClassConcreteCharge ActualZeroClassValueConservation

theorem exactConcreteOutputState : ExactConcreteOutputState := by
  intro f B selected ρ ordered C r constant raw xs annotations paid bounded normalized
    aligned ready actualC zero
  dsimp only
  intro tails
  obtain ⟨moved,ledger,x₀,q,hm,movedReads,anchor,originLedger,equations,replacement,charge⟩ :=
    exactConcreteZeroClassCharge f B selected ρ ordered C r constant raw xs annotations
      paid bounded normalized aligned ready actualC zero tails
  obtain ⟨afterReads,sameRow,sameValue⟩ :=
    exactConcreteValueConservation f B selected ρ C r constant raw xs annotations moved
      paid normalized aligned ready zero hm movedReads
  have originalRanks := exactOutputRankProvenance f ρ C raw xs annotations moved
    paid normalized aligned hm
  refine ⟨moved,ledger,x₀,q,hm,movedReads,anchor,originLedger,equations,afterReads,originalRanks,
    ?_,sameValue,sameRow.symm,replacement,charge⟩
  intro rd member
  obtain ⟨prior,original,rank⟩ := originalRanks rd member
  rw [rank]
  exact bounded prior original

theorem fullActualZeroClassOutputState : FullActualZeroClassOutputState :=
  ⟨exactOutputRankProvenance,exactConcreteOutputState⟩

end LogicLineages.PermittedControl.ActualZeroClassOutputState
