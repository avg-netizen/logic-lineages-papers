module
public import LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransitionTargets
import LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransitionAssemblyProof
import LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransitionRanksProof
import LogicLineages.PermittedControl.ActualNormalizedTapeDispositionValueProof
import LogicLineages.PermittedControl.ActualShortCountCleanupChargeColumnsProof
import LogicLineages.PermittedControl.ActualShortCountCleanupProof
import LogicLineages.PermittedControl.InnerTerminationProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransition
open scoped Classical
open OrdinalComparison ActualNormalizedTape ActualNormalizedTapeDisposition
open ActualZeroClassReplacement ActualRankedRowColumns ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualZeroClassOutputState ActualZeroClassConcreteAssembly
open ActualShortCountCleanupCharge ActualShortCountCleanup InnerTerminationTargets

theorem exactTapeZeroTransition : ExactTapeZeroTransition := by
  intro f B selected ρ strict C r constant raw xs annotations bounded tape aligned ready actualC zero
  dsimp only
  intro transfer
  obtain ⟨moved,ledger,x₀,q,moves,movedReads,anchor,origins,equations,replacement⟩ :=
    exactTapeZeroAssembly f B selected ρ strict C r constant raw xs annotations
      bounded tape aligned ready actualC zero transfer
  obtain ⟨live,sameRow,sameValue⟩ := exactTapeValueConservation f B selected ρ C r constant
    raw xs annotations moved tape aligned ready zero moves movedReads
  have ranks := exactTapeOutputRanks f ρ C raw xs annotations moved tape aligned moves
  let before := outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations ++ moved
  let installed := constant + (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2
  have bound : ∀ rd ∈ before, rd.1.2.rank < r := by
    intro rd member
    obtain ⟨prior,beforeRaw,rank⟩ := ranks rd member
    rw [rank]
    exact bounded prior beforeRaw
  have rep : ZeroClassReplacement (rankedRow r constant raw) (rankedRow r installed before) :=
    sameRow ▸ replacement
  obtain ⟨weakCount,weakValue,strictCharge⟩ :=
    InnerTerminationProof.fullInnerTermination (ValueKey r) (NONote × NONote) r
      (rankedRow r constant raw) (rankedRow r installed before) rep
  refine ⟨moved,ledger,x₀,q,moves,movedReads,anchor,origins,equations,live,ranks,bound,
    sameValue,sameRow.symm,rep,weakCount,weakValue,strictCharge,?_⟩
  change CleanedOutput f ρ r constant raw installed before
  obtain ⟨kept,afterReads,long,provenance,conserved⟩ :=
    exactShortCountCleanup f B selected ρ installed raw before live
  obtain ⟨valueEq,countEq,_,countClean,valueClean⟩ := exactCleanupCharge r installed before
  have valueWeak := valueClean.le
  exact ⟨kept,afterReads,long,provenance ranks,fun rd member => bound rd (kept.subset member),
    sameValue.trans conserved,valueEq,countEq,countClean.trans weakCount,valueWeak.trans weakValue,
    (Nat.add_le_add countClean valueWeak).trans_lt strictCharge⟩

end LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransition
