module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTestProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdvanceWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparseRoundLeastChecks (exact_CoveredLeastIdempotent)
open NumberedWindowInternalSparsePathSuccessfulAdvanceChecks (exact_OpenSuccessfulAdvanceCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalSparsePositiveWindowChecks (exact_PositiveWindows)
open NumberedWindowInternalSparseAdvanceWindowChecks (exact_SuccessfulAdvanceWindowsFromRetained)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparseCoveredWindowTargets (coveredWindow)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCanonicalCoordinatesTargets

theorem exact_CoordinateCalibration : ExactCoordinateCalibration :=
  NumberedWindowInternalSparseCanonicalCoordinatesTestProof.calibration

theorem exact_OpenCoordinateTest : ExactOpenCoordinateTest :=
  NumberedWindowInternalSparseCanonicalCoordinatesTestProof.openTest

theorem exact_CanonicalAdvance : ExactCanonicalAdvance := by
  intro C s baseX baseW root other syntaxProg W X least body α Γ ctx ty source hop target
  let raw := typedRaw5 root other W syntaxProg
  let accepted := selectedGraph raw least (suc target) ctx ty (suc source) hop
  let Δ := accepted :: Γ
  have h : Derivation body Δ accepted := Derivation.hypothesis List.mem_cons_self
  obtain ⟨windows⟩ := exact_SuccessfulAdvanceWindowsFromRetained exact_RetainedPredecessor
    C X W root other syntaxProg s body α Δ ctx ty source hop target
  have guarded := Derivation.implicationElimination windows h
  obtain ⟨invert⟩ := exact_OpenSuccessfulAdvanceCalls body raw least α ctx ty source hop target
  have actual := closedApply ⟨Derivation.conjunctionLeft invert⟩ ⟨h⟩
  have result : Nonempty (Derivation body Δ (windowAt (canonicalCoordinates W least) ctx ty source ⊓
       windowAt (canonicalCoordinates W least) ctx ty target)) := by
    apply reportCases raw least ctx ty source hop target _ actual
    intro β j Θ q w r keep fields
    rw [conjunctionRename,windowRename,windowRename]
    have guards := renameInto ⟨guarded⟩ j Θ keep
    rw [conjunctionRename,windowRename,windowRename] at guards
    obtain ⟨g⟩ := guards
    obtain ⟨f⟩ := fields
    have values := Derivation.conjunctionRight (Derivation.conjunctionRight f)
    have fix := exact_CoveredLeastIdempotent C s baseX baseW body β Θ (ctx.relabel j) (ty.relabel j)
    obtain ⟨left⟩ := fix q (source.relabel j)
    obtain ⟨right⟩ := fix r (target.relabel j)
    have checked := exact_OpenCoordinateTest W least body β Θ (ctx.relabel j) (ty.relabel j)
    obtain ⟨src⟩ := checked (source.relabel j)
    obtain ⟨dst⟩ := checked (target.relabel j)
    exact ⟨Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (Derivation.conjunctionRight src) (Derivation.conjunctionIntroduction
        (Derivation.conjunctionLeft g) (Derivation.implicationElimination left (Derivation.conjunctionLeft values))))
      (Derivation.implicationElimination (Derivation.conjunctionRight dst) (Derivation.conjunctionIntroduction
        (Derivation.conjunctionRight g) (Derivation.implicationElimination right (Derivation.conjunctionRight values))))⟩
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

theorem exact_CanonicalPositive : ExactCanonicalPositive := by
  intro C s baseX baseW root other syntaxProg body α Γ ctx ty a cert b W X least raw
  exact exact_PositiveWindows raw least (canonicalCoordinates W least)
    (exact_CanonicalAdvance C s baseX baseW root other syntaxProg) body α Γ ctx ty a cert b

#print axioms exact_CoordinateCalibration
#print axioms exact_OpenCoordinateTest
#print axioms exact_CanonicalAdvance
#print axioms exact_CanonicalPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesChecks
