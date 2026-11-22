module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnContinuationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverChildOwnScopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalAuxOwnContinuationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (boundBody)
open NumberedWindowInternalCoverSharedOwnScratchTargets (ChildOwnInputs OwnOccurrence)
open NumberedWindowInternalCoverSharedMeasureChildrenTargets (SelectedMeasureData)
open NumberedWindowInternalCoverSharedMeasureChildCasesProof (moveMeasuredChild)
open NumberedWindowInternalCoverChildOwnScopeProof (exact_OpenCoverChildOwnScopeCases moveOwn moveLocal)
open NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof (fromActualBounds boundsRename)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent moveTypeMember)
open NumberedWindowInternalCoverLocalOwnContinuationTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atFunction (V : Program 1) (R : Program 4) (W : Program 3) (s : Settings)
    (p vertices ctx dom cod fn arg ma df da bf ba fState fTerms fArgs : OTerm α)
    (parent : ActualOwnParent V R s body Γ (auxiliaryTerm dom cod fn arg) p vertices)
    (f : OwnOccurrence s body Γ df bf fState fTerms fArgs fn)
    (argLocal : ChildOwnInputs V R W s body Γ ctx dom arg)
    (argData : SelectedMeasureData R body Γ arg ma da ba)
    (bounds : Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba))))
    (domain : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)))
    (codomain : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod))) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenCoverChildOwnScopeCases V R W s body α Γ
    ctx dom arg ma da ba _ argLocal argData
  intro β j Δ aState aTerms aArgs keep a
  rw [graphRename,auxiliaryRename]
  have parent' := moveParent V R s j keep parent
  rw [auxiliaryRename] at parent'
  have domain' := moveTypeMember s j keep domain
  have codomain' := moveTypeMember s j keep codomain
  have f' := moveOwn s j keep f
  have bounds' := renameInto bounds j Δ keep
  rw [boundsRename] at bounds'
  exact fromActualBounds V (selectedMeasure R) s
    (p.relabel j) (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j) aState aTerms aArgs (vertices.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    f' a bounds' domain' codomain' parent'.valid parent'.measured parent'.held

theorem exact_OpenCoverLocalAuxOwnContinuation : ExactOpenCoverLocalAuxOwnContinuation := by
  intro V R W s body α Γ p vertices ctx dom cod fn arg mf ma df da bf ba
    parent fnLocal argLocal fnData argData bounds domain codomain
  apply exact_OpenCoverChildOwnScopeCases V R W s body α Γ
    ctx (rawCons dom cod) fn mf df bf _ fnLocal fnData
  intro β j Δ fState fTerms fArgs keep f
  rw [graphRename,auxiliaryRename]
  have parent' := moveParent V R s j keep parent
  rw [auxiliaryRename] at parent'
  have domain' := moveTypeMember s j keep domain
  have codomain' := moveTypeMember s j keep codomain
  have argLocal' := moveLocal V R W s j keep argLocal
  have argData' := moveMeasuredChild R j Δ keep argData
  have bounds' := renameInto bounds j Δ keep
  rw [boundsRename] at bounds'
  exact atFunction V R W s (p.relabel j) (vertices.relabel j) (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    (ma.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j)
    fState fTerms fArgs parent' f argLocal' argData' bounds' domain' codomain'

#print axioms exact_OpenCoverLocalAuxOwnContinuation

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalAuxOwnContinuationProof
