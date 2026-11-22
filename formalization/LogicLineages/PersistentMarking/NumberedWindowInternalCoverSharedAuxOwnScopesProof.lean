module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverChildOwnScopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxOwnScopesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof (ihRename)
open SourceComputabilityFormulaSupportProof (existsOne)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (boundBody)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedSyntax sharedMeasure sharedMeasureUpdate)
open NumberedWindowInternalCoverSharedMeasureChildrenTargets (SelectedMeasureData)
open NumberedWindowInternalCoverSharedMeasureChildCasesProof (moveMeasuredChild)
open NumberedWindowInternalCoverChildOwnScopeProof (exact_OpenCoverChildOwnScopeCases moveOwn moveLocal)
open NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof (fromActualBounds boundsRename)
open NumberedWindowInternalCoverSharedOwnScratchTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem moveAuxInputs (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    {p vertices ctx dom cod fn arg : OTerm α} (paid : AuxInputs V TV M B TW s body Γ p vertices ctx dom cod fn arg) :
    AuxInputs V TV M B TW s body Δ (p.relabel j) (vertices.relabel j) (ctx.relabel j) (dom.relabel j)
      (cod.relabel j) (fn.relabel j) (arg.relabel j) := by
  constructor
  · have d := renameInto paid.valid j Δ keep
    simpa only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] using d
  · have d := renameInto paid.measured j Δ keep
    simpa only [unaryRename,auxiliaryRename] using d
  · have d := renameInto paid.typed j Δ keep
    simpa only [windowRename,auxiliaryRename] using d
  · have d := renameInto paid.fnIH j Δ keep
    simpa only [ihRename,rawConsRename] using d
  · have d := renameInto paid.argIH j Δ keep
    simpa only [ihRename] using d
  · have d := renameInto paid.domMember j Δ keep
    simpa only [graphRename,typesTerm,numeralRename] using d
  · have d := renameInto paid.codMember j Δ keep
    simpa only [graphRename,typesTerm,numeralRename] using d
  · have d := renameInto paid.held j Δ keep
    simpa only [unaryRename,auxiliaryRename] using d

private theorem atFunction (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (p vertices ctx dom cod fn arg ma df da bf ba fState fTerms fArgs : OTerm α)
    (paid : AuxInputs V TV M B TW s body Γ p vertices ctx dom cod fn arg)
    (f : OwnOccurrence s body Γ df bf fState fTerms fArgs fn)
    (argLocal : ChildOwnInputs (sharedSyntax V TV) (sharedMeasureUpdate M) (strictAuxWindow B TW) s body Γ ctx dom arg)
    (argData : SelectedMeasureData (sharedMeasureUpdate M) body Γ arg ma da ba)
    (bounds : Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenCoverChildOwnScopeCases (sharedSyntax V TV) (sharedMeasureUpdate M) (strictAuxWindow B TW) s body α Γ
    ctx dom arg ma da ba _ argLocal argData
  intro β j Δ aState aTerms aArgs keep a
  rw [graphRename,auxiliaryRename]
  have paid' := moveAuxInputs V TV M B TW s j keep paid
  have f' := moveOwn s j keep f
  have bounds' := renameInto bounds j Δ keep
  rw [boundsRename] at bounds'
  exact fromActualBounds (sharedSyntax V TV) (sharedMeasure M) s
    (p.relabel j) (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j) aState aTerms aArgs (vertices.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    f' a bounds' paid'.domMember paid'.codMember paid'.valid paid'.measured paid'.held

theorem fromSharedMeasured (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (p vertices ctx dom cod fn arg mf ma df da bf ba : OTerm α)
    (paid : AuxInputs V TV M B TW s body Γ p vertices ctx dom cod fn arg)
    (fnLocal : ChildOwnInputs (sharedSyntax V TV) (sharedMeasureUpdate M) (strictAuxWindow B TW) s body Γ ctx (rawCons dom cod) fn)
    (argLocal : ChildOwnInputs (sharedSyntax V TV) (sharedMeasureUpdate M) (strictAuxWindow B TW) s body Γ ctx dom arg)
    (fnData : SelectedMeasureData (sharedMeasureUpdate M) body Γ fn mf df bf)
    (argData : SelectedMeasureData (sharedMeasureUpdate M) body Γ arg ma da ba)
    (bounds : Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenCoverChildOwnScopeCases (sharedSyntax V TV) (sharedMeasureUpdate M) (strictAuxWindow B TW) s body α Γ
    ctx (rawCons dom cod) fn mf df bf _ fnLocal fnData
  intro β j Δ fState fTerms fArgs keep f
  rw [graphRename,auxiliaryRename]
  have paid' := moveAuxInputs V TV M B TW s j keep paid
  have argLocal' := moveLocal (sharedSyntax V TV) (sharedMeasureUpdate M) (strictAuxWindow B TW) s j keep argLocal
  have argData' := moveMeasuredChild (sharedMeasureUpdate M) j Δ keep argData
  have bounds' := renameInto bounds j Δ keep
  rw [boundsRename] at bounds'
  exact atFunction V TV M B TW s (p.relabel j) (vertices.relabel j) (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    (ma.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j)
    fState fTerms fArgs paid' f argLocal' argData' bounds'

#print axioms fromSharedMeasured

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxOwnScopesProof
