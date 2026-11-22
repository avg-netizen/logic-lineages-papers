module
public import LogicLineages.PermittedControl.ActualShortCountCleanupChargeTargets
import LogicLineages.PermittedControl.ActualShortCountCleanupChargeColumnsProof
import LogicLineages.PermittedControl.ActualZeroClassOutputStateProof
import LogicLineages.PermittedControl.ActualShortCountCleanupProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualShortCountCleanupCharge
open scoped Classical
open ActualZeroClassReplacement ActualRankedRowColumns ActualZeroClassRecombinedRow
open ActualZeroClassOutputState ActualShortCountCleanup InnerTerminationTargets

theorem exactConcreteLongOutputState : ExactConcreteLongOutputState := by
  intro f B selected ρ strict C r constant raw xs annotations paid bounded normalized
    aligned ready actualC zero
  dsimp only
  intro transfer
  obtain ⟨moved,ledger,x₀,q,moves,movedReads,anchor,origins,equations,live,ranks,bound,
    sameValue,concrete,replacement,weakCount,weakValue,strictCharge⟩ :=
    exactConcreteOutputState f B selected ρ strict C r constant raw xs annotations
      paid bounded normalized aligned ready actualC zero transfer
  refine ⟨moved,ledger,x₀,q,moves,movedReads,anchor,origins,equations,live,ranks,bound,
    sameValue,concrete,replacement,weakCount,weakValue,strictCharge,?_⟩
  let before := outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations ++ moved
  let installed := constant + (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2
  change CleanedOutput f ρ r constant raw installed before
  obtain ⟨kept,afterReads,long,provenance,conserved⟩ :=
    exactShortCountCleanup f B selected ρ installed raw before live
  obtain ⟨valueEq,countEq,_,countClean,valueClean⟩ := exactCleanupCharge r installed before
  have valueWeak := valueClean.le
  exact ⟨kept,afterReads,long,provenance ranks,fun rd member => bound rd (kept.subset member),
    sameValue.trans conserved,valueEq,countEq,countClean.trans weakCount,valueWeak.trans weakValue,
    (Nat.add_le_add countClean valueWeak).trans_lt strictCharge⟩

theorem fullActualShortCountCleanupCharge : FullActualShortCountCleanupCharge :=
  ⟨exactCleanupGroupedCoefficients,exactCleanupCharge,exactConcreteLongOutputState⟩

end LogicLineages.PermittedControl.ActualShortCountCleanupCharge
