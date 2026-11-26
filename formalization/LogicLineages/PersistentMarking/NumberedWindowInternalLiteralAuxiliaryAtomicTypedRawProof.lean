module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedGuardReturnProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTerminalRunProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration)
open NumberedWindowInternalSparseRawTick (rootCall tagFiveTest)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot termShape chosenFrame)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_TypedRaw5Calibration)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalLiteralAtomicAddressReportProof (renameFree renameBottom)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)
open NumberedWindowInternalLiteralAtomicTickNumericProof
  (atomicRoot atomicFallback exact_LiteralAtomicRootCalibration exact_LiteralAtomicFallbackCalibration)
open NumberedWindowInternalLiteralAtomicTickOpenProof
  (exact_OpenLiteralAtomicRootFreeTarget exact_OpenLiteralAtomicFallbackFree exact_OpenLiteralAtomicTickBottomCallbacks)
open NumberedWindowInternalLiteralAtomicFrameZeroProof
  (exact_OpenLiteralAtomicAuxReject exact_OpenLiteralBottomTests exact_OpenLiteralAtomicNoFunctionFrame)
open NumberedWindowInternalLiteralAtomicTerminalRunProof (exact_OpenLiteralTerminalOwnRunRoot)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeReports)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux auxiliaryFallback)
open NumberedWindowInternalLiteralAuxFallbackNumericProof (exact_AuxiliaryFallback)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open NumberedWindowInternalLiteralAtomicTypedRawProof (exact_OpenLiteralRootCallPayload)
open NumberedWindowInternalLiteralAtomicTypedGuardReturnProof (RawAtoms)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def auxiliaryAtomicTypedRaw (p other W : Program 3) (V : Program 1) : Program 5 :=
  typedRaw5 (atomicRoot p) (auxiliaryFallback (atomicFallback other)) W V

theorem exact_LiteralAuxiliaryAtomicTypedRawCalibration (xs : Entries) (s : Settings) (p other W : Program 3)
    (V : Program 1) (fit : ActualRoot (root xs s) p) (fall : ActualFallback other)
    (window : ActualPackedWindow s W) (syntaxFit : ActualRawSyntax V) :
    ActualRawCalibration xs s (auxiliaryAtomicTypedRaw p other W V) :=
  exact_TypedRaw5Calibration xs s (atomicRoot p) (auxiliaryFallback (atomicFallback other)) W V
    (exact_LiteralAtomicRootCalibration xs s p fit) (exact_AuxiliaryFallback (atomicFallback other) (exact_LiteralAtomicFallbackCalibration other fall))
    syntaxFit window

/-- The auxiliary fallback is outermost so that the original exact
contextual inverse can open it, while the inner atom test still makes
both atom terminal cases available on the actual callback. -/
private theorem atomFallback (other : Program 3) (q w r : OTerm α)
    (shape : D B Γ (unary termShape z q))
    (base : D B Γ (programGraph (atomicFallback other) z ![q,w,r])) :
    D B Γ (programGraph (auxiliaryFallback (atomicFallback other)) z ![q,w,r]) :=
  zeroBranchIntro sourceIsAux (atomicFallback other)
    (branch tagFiveTest (constantZero 3) chosenFrame) z ![q,w,r]
    (onTape termShape 0 z ![q,w,r] shape) base

private theorem own (p other W : Program 3) (V : Program 1) (ctx ty q w r : OTerm α)
    (held : D B Γ (programGraph (auxiliaryAtomicTypedRaw p other W V) (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (programGraph (ownRun (atomicRoot p) (auxiliaryFallback (atomicFallback other))) (suc z) ![q,w,r]) := by
  obtain ⟨rel⟩ := exact_OpenTypedRaw5 B (atomicRoot p) (auxiliaryFallback (atomicFallback other)) W V α Γ ctx ty q w r
  obtain ⟨h⟩ := held
  exact ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft
    (Derivation.implicationElimination (Derivation.conjunctionLeft rel) h))⟩

/-- A genuine free raw child of the per-tick guarded checker has the
expected bottom destination without needing an outer raw guard. -/
theorem exact_OpenLiteralAuxiliaryAtomicTypedFreeTarget (p other W : Program 3) (V : Program 1)
    (ctx ty t n w r : OTerm α)
    (held : D B Γ (programGraph (auxiliaryAtomicTypedRaw p other W V) (suc z) ![ctx,ty,freeTerm t n,w,r])) :
    D B Γ (eqn r (bottomTerm t)) := by
  let q := freeTerm t n
  have fast := exact_OpenLiteralAtomicNoFunctionFrame q w r (exact_OpenLiteralAtomicAuxReject (B := B) (Γ := Γ) t n).1
  have fallback := atomFallback other q w r (exact_OpenLiteralAtomicAuxReject (B := B) (Γ := Γ) t n).1
    (exact_OpenLiteralAtomicFallbackFree other q w r (freeReports (B := B) (Γ := Γ) t n).1)
  have rootYes := exact_OpenLiteralTerminalOwnRunRoot (atomicRoot p) (auxiliaryFallback (atomicFallback other)) q w r fast fallback
    (own p other W V ctx ty q w r held)
  apply exact_OpenLiteralRootCallPayload (atomicRoot p) q w r (eqn r (bottomTerm t)) rootYes
  intro β j Δ payload keep h
  rw [eqnRelabel,renameBottom]
  rw [show q.relabel j = freeTerm (t.relabel j) (n.relabel j) from renameFree t n j] at h
  exact exact_OpenLiteralAtomicRootFreeTarget p (t.relabel j) (n.relabel j) payload (r.relabel j) h

theorem exact_OpenLiteralAuxiliaryAtomicTypedBottomReject (p other W : Program 3) (V : Program 1)
    (ctx ty t w r : OTerm α)
    (held : D B Γ (programGraph (auxiliaryAtomicTypedRaw p other W V) (suc z) ![ctx,ty,bottomTerm t,w,r])) :
    D B Γ ⊥ := by
  let q := bottomTerm t
  have fast := exact_OpenLiteralAtomicNoFunctionFrame q w r (exact_OpenLiteralAtomicAuxReject (B := B) (Γ := Γ) t t).2
  obtain ⟨no,yes⟩ := exact_OpenLiteralBottomTests (B := B) (Γ := Γ) t
  have fallback := atomFallback other q w r (exact_OpenLiteralAtomicAuxReject (B := B) (Γ := Γ) t t).2
    (exact_OpenLiteralAtomicTickBottomCallbacks p other q w r no yes).2
  have rootYes := exact_OpenLiteralTerminalOwnRunRoot (atomicRoot p) (auxiliaryFallback (atomicFallback other)) q w r fast fallback
    (own p other W V ctx ty q w r held)
  apply exact_OpenLiteralRootCallPayload (atomicRoot p) q w r ⊥ rootYes
  intro β j Δ payload keep h
  rw [show q.relabel j = bottomTerm (t.relabel j) from renameBottom t j] at h
  obtain ⟨nof,bot⟩ := exact_OpenLiteralBottomTests (B := B) (Γ := Δ) (t.relabel j)
  have declined := (exact_OpenLiteralAtomicTickBottomCallbacks p other (bottomTerm (t.relabel j))
    payload (r.relabel j) nof bot).1
  obtain ⟨no⟩ := valueUnique (atomicRoot p) (suc z) z ![bottomTerm (t.relabel j),payload,r.relabel j] h declined
  exact ⟨Derivation.explosion (sucNeZeroApply no)⟩

theorem exact_OpenLiteralAuxiliaryAtomicRawAtoms (p other W : Program 3) (V : Program 1) :
    RawAtoms (auxiliaryAtomicTypedRaw p other W V) :=
  ⟨fun B α Γ => exact_OpenLiteralAuxiliaryAtomicTypedFreeTarget p other W V,
    fun B α Γ => exact_OpenLiteralAuxiliaryAtomicTypedBottomReject p other W V⟩

#print axioms exact_OpenLiteralAuxiliaryAtomicRawAtoms
#print axioms exact_LiteralAuxiliaryAtomicTypedRawCalibration
#print axioms exact_OpenLiteralAuxiliaryAtomicTypedFreeTarget
#print axioms exact_OpenLiteralAuxiliaryAtomicTypedBottomReject
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof
