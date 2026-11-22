module
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationEdgeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricInstallationChecks
open NumberedWindowInternalSparseCoverInstallationTargets
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeChecks (exact_GuardedExchangeCalibration)
open NumberedWindowInternalSparseDirectedInstallationChecks (exact_DirectedInstallation)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseInstalledOccurrenceChecks (exact_UnconditionalCoverOccurrence)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_ReinstallCalibratedLeast)
open NumberedWindowInternalSparseApplicationReinstallChecks (exact_ReinstallGuardedApplicationTuple)
open NumberedWindowInternalSparsePackedLeastNumericChecks (exact_PackedLeastComposition)
open NumberedWindowInternalSparseMinimumEdgeChecks (exact_MinimumEdgeBound)
open NumberedWindowInternalSparsePositiveWindowChecks (exact_PhysicalPositiveWindowsFromRetained)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)

open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedWindowInternalSparseSymmetricExchangeTargets (swapExchange pairedExchange)
open NumberedWindowInternalSparseSymmetricInstallationTargets
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowExchangeAlgorithm (bits)

theorem exact_PairedCalibration : ExactPairedCalibration := by
  intro s X symmetric hX a b
  let xs := List.Vector.ofFn (exchangeTape a b)
  have rev : evaluate (swapExchange X) xs = evaluate X (List.Vector.ofFn (exchangeTape b a)) := by
    change evaluate X (List.Vector.ofFn (fun i : Fin 2 =>
      evaluate ((![.projection 1,.projection 0] : Fin 2 → Program 2) i) xs)) = _
    rw [vectorTwo,vectorTwo]
    rfl
  have same := NumberedWindowRawExchangeSymmetryChecks.exact_RawExchangeSymmetry s.equivalentHeads symmetric a b
  change evaluate (pairedExchange X) xs = _
  rw [pairedExchange,actualConjunctionEvaluation,rev,hX b a,← same]
  have fwd : evaluate X xs = ((bits s.equivalentHeads a b).1).toNat := hX a b
  rw [fwd]
  cases (bits s.equivalentHeads a b).1 <;> rfl

theorem exact_SymmetricInstallation : ExactSymmetricInstallation := by
  obtain ⟨C,cover,tuples⟩ := exact_DirectedInstallation
  refine ⟨C,cover,?_⟩
  intro entries s W valid symmetric
  obtain ⟨i,j,cv,tv,syntaxProg,baseX,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hBase,_,typedTuple,_⟩ := tuples entries s W valid
  let paired := pairedExchange baseX
  let X := guardedExchange C s paired
  let raw := typedRaw5 root other windowProg syntaxProg
  let least := packedLeastProgram C X windowProg s
  have hPaired := exact_PairedCalibration s baseX symmetric hBase
  have exchange := exact_GuardedExchangeCalibration C s paired cover hPaired
  have cal := exact_PackedLeastComposition s C X windowProg cover exchange hWindow
  have precise := exact_ReinstallCalibratedLeast entries s W valid i j cv tv d oldCore
    raw oldLeast least v typedTuple cal
  obtain ⟨chosen,updated⟩ := exact_ReinstallGuardedApplicationTuple entries s W valid i j cv tv d oldCore raw least v precise
  exact ⟨i,j,cv,tv,syntaxProg,baseX,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hBase,exchange,cal,typedTuple,precise,chosen,updated,
    exact_UnconditionalCoverOccurrence C X windowProg s,
    exact_MinimumEdgeBound exact_RetainedPredecessor C X windowProg s,
    exact_PhysicalPositiveWindowsFromRetained exact_RetainedPredecessor C X windowProg root other syntaxProg s,
    NumberedWindowInternalSparseCoverInstallationEdgeProof.edgeCover C s paired windowProg,
    NumberedWindowInternalSparseAdjacentMinimumChecks.exact_EdgeMinimumOrder C s paired windowProg,
    NumberedWindowInternalSparseAdjacentMinimumChecks.exact_MutualEdgeMinimumEquality C s paired windowProg,
    NumberedWindowInternalSparseSymmetricExchangeChecks.exact_PairedEdgeMinimumEquality C s baseX windowProg⟩

#print axioms exact_PairedCalibration
#print axioms exact_SymmetricInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricInstallationChecks
