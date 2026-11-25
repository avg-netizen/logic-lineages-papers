module
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedRawProof
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
open NumberedWindowInternalSparseRawTick (rootCall)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
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

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def atomicTypedRaw (p other W : Program 3) (V : Program 1) : Program 5 :=
  typedRaw5 (atomicRoot p) (atomicFallback other) W V

theorem exact_LiteralAtomicTypedRawCalibration (xs : Entries) (s : Settings) (p other W : Program 3)
    (V : Program 1) (fit : ActualRoot (root xs s) p) (fall : ActualFallback other)
    (window : ActualPackedWindow s W) (syntaxFit : ActualRawSyntax V) :
    ActualRawCalibration xs s (atomicTypedRaw p other W V) :=
  exact_TypedRaw5Calibration xs s (atomicRoot p) (atomicFallback other) W V
    (exact_LiteralAtomicRootCalibration xs s p fit) (exact_LiteralAtomicFallbackCalibration other fall)
    syntaxFit window

theorem exact_OpenLiteralRootCallPayload (p : Program 3) (q w r : OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph (rootCall p) (suc z) ![q,w,r]))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph p (suc z) ![q.relabel j,payload,r.relabel j]) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let fs : Fin 3 → Program 3 := ![.projection 0,frameSlot 0 1,.projection 2]
  let xs : Fin 3 → OTerm α := ![q,w,r]
  obtain ⟨selected⟩ := normalizeRecover (.composition p fs) xs held
  apply programCases (frameSlot 0 1) xs goal
  intro β j Δ payload keep part
  simp only [xs,tripleInputsRename] at part
  have report := renameInto ⟨selected⟩ j Δ keep
  simp only [xs,programRename,tripleInputsRename,sucRelabel,zRelabel] at report
  let tape : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  have exactRoot := compositionRecover p fs (suc z) tape ![q.relabel j,payload,r.relabel j] report
    (fun a => Fin.cases (projectionValue 0 tape) (Fin.cases part
      (Fin.cases (projectionValue 2 tape) (fun x => Fin.elim0 x))) a)
  exact k β j Δ payload keep exactRoot

private theorem own (p other W : Program 3) (V : Program 1) (ctx ty q w r : OTerm α)
    (held : D B Γ (programGraph (atomicTypedRaw p other W V) (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (programGraph (ownRun (atomicRoot p) (atomicFallback other)) (suc z) ![q,w,r]) := by
  obtain ⟨rel⟩ := exact_OpenTypedRaw5 B (atomicRoot p) (atomicFallback other) W V α Γ ctx ty q w r
  obtain ⟨h⟩ := held
  exact ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft
    (Derivation.implicationElimination (Derivation.conjunctionLeft rel) h))⟩

/-- A genuine free raw child of the per-tick guarded checker has the
expected bottom destination without needing an outer raw guard. -/
theorem exact_OpenLiteralAtomicTypedFreeTarget (p other W : Program 3) (V : Program 1)
    (ctx ty t n w r : OTerm α)
    (held : D B Γ (programGraph (atomicTypedRaw p other W V) (suc z) ![ctx,ty,freeTerm t n,w,r])) :
    D B Γ (eqn r (bottomTerm t)) := by
  let q := freeTerm t n
  have fast := exact_OpenLiteralAtomicNoFunctionFrame q w r (exact_OpenLiteralAtomicAuxReject (B := B) (Γ := Γ) t n).1
  have fallback := exact_OpenLiteralAtomicFallbackFree other q w r (freeReports (B := B) (Γ := Γ) t n).1
  have rootYes := exact_OpenLiteralTerminalOwnRunRoot (atomicRoot p) (atomicFallback other) q w r fast fallback
    (own p other W V ctx ty q w r held)
  apply exact_OpenLiteralRootCallPayload (atomicRoot p) q w r (eqn r (bottomTerm t)) rootYes
  intro β j Δ payload keep h
  rw [eqnRelabel,renameBottom]
  rw [show q.relabel j = freeTerm (t.relabel j) (n.relabel j) from renameFree t n j] at h
  exact exact_OpenLiteralAtomicRootFreeTarget p (t.relabel j) (n.relabel j) payload (r.relabel j) h

theorem exact_OpenLiteralAtomicTypedBottomReject (p other W : Program 3) (V : Program 1)
    (ctx ty t w r : OTerm α)
    (held : D B Γ (programGraph (atomicTypedRaw p other W V) (suc z) ![ctx,ty,bottomTerm t,w,r])) :
    D B Γ ⊥ := by
  let q := bottomTerm t
  have fast := exact_OpenLiteralAtomicNoFunctionFrame q w r (exact_OpenLiteralAtomicAuxReject (B := B) (Γ := Γ) t t).2
  obtain ⟨no,yes⟩ := exact_OpenLiteralBottomTests (B := B) (Γ := Γ) t
  have fallback := (exact_OpenLiteralAtomicTickBottomCallbacks p other q w r no yes).2
  have rootYes := exact_OpenLiteralTerminalOwnRunRoot (atomicRoot p) (atomicFallback other) q w r fast fallback
    (own p other W V ctx ty q w r held)
  apply exact_OpenLiteralRootCallPayload (atomicRoot p) q w r ⊥ rootYes
  intro β j Δ payload keep h
  rw [show q.relabel j = bottomTerm (t.relabel j) from renameBottom t j] at h
  obtain ⟨nof,bot⟩ := exact_OpenLiteralBottomTests (B := B) (Γ := Δ) (t.relabel j)
  have declined := (exact_OpenLiteralAtomicTickBottomCallbacks p other (bottomTerm (t.relabel j))
    payload (r.relabel j) nof bot).1
  obtain ⟨no⟩ := valueUnique (atomicRoot p) (suc z) z ![bottomTerm (t.relabel j),payload,r.relabel j] h declined
  exact ⟨Derivation.explosion (sucNeZeroApply no)⟩

#print axioms exact_OpenLiteralRootCallPayload
#print axioms exact_LiteralAtomicTypedRawCalibration
#print axioms exact_OpenLiteralAtomicTypedFreeTarget
#print axioms exact_OpenLiteralAtomicTypedBottomReject
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedRawProof
