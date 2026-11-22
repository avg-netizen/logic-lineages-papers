module
public import LogicLineages.PermittedControl.ActualNormalizedTapeDispositionTargets
import LogicLineages.PermittedControl.ActualZeroClassValueConservationArithmeticProof
import LogicLineages.PermittedControl.ActualZeroClassRecombinedRowPartitionProof
import LogicLineages.PermittedControl.ActualZeroClassReplacementRowProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeDisposition
open ActualMixedRowLeadingSum ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow

open ActualNormalizedTape ActualZeroClassValueConservation

theorem exactTapeValueConservation : ExactTapeValueConservation := by
  intro f B selected ρ C r constant raw xs annotations moved tape
  dsimp only
  intro aligned ready zero movedAt movedReads
  let terms := xs.map Prod.fst
  let values := xs.map Prod.snd
  let ps := cohort f C terms annotations
  let outside := outsideCohort f C terms values annotations
  let out := replaceRow f C terms values annotations
  let parts := rowParts f C terms values annotations
  have originalValue := tape.sameValue
  have equation := exactDoubledRowIdentity f ρ C terms values annotations aligned
  change 2 * readSum xs = parts.1 * (C : Int) + 2 * parts.2 at equation
  change parts.1 = 0 at zero
  rw [zero,zero_mul,zero_add] at equation
  have remainderValue : readSum xs = parts.2 := by omega
  obtain ⟨_, retainedValue⟩ := exactRetainedRemainder f B selected ρ C
    terms values annotations aligned ready
  change out.2 + readSum out.1 = parts.2 at retainedValue
  obtain ⟨_,_,outsideReads,partition⟩ := exactResidualPartition f B selected ρ C
    terms values annotations aligned ready
  change readSum outside + readSum (ps.map SurvivingPrefix.asRead) = readSum out.1 at partition
  have moves := exactMovedValue f ρ (leastPrefix ps) ps moved movedAt
  have outputValue : readSum (outside ++ moved) = readSum out.1 := by
    rw [appendReadSum,← moves,partition]
  refine ⟨appendLiftedReads f ρ outside moved outsideReads movedReads,rfl,?_⟩
  change constant + readSum raw = (constant + out.2) + readSum (outside ++ moved)
  rw [originalValue,remainderValue,outputValue,← retainedValue,add_assoc]

end LogicLineages.PermittedControl.ActualNormalizedTapeDisposition
