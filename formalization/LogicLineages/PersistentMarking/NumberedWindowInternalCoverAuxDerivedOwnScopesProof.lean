module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureAlignProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnScopesProof
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
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureParentTargets (AuxMeasureChild)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (measureRename)
open NumberedWindowInternalChosenAuxMeasureAlignProof (moveChild)
open NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof (ihRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (MeasuredChild)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredProof (exact_OpenSelectedGrammarAuxScratchMeasured)
open NumberedWindowInternalCoverAuxDerivedOwnChildProof
  (exact_OpenCoverAuxMeasuredChildCases moveMeasured moveLocal)
open NumberedWindowInternalCoverAuxDerivedOwnTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem moveInputs (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    {p vertices ctx dom cod fn arg : OTerm α} (paid : Inputs V TV M B TW s body Γ p vertices ctx dom cod fn arg) :
    Inputs V TV M B TW s body Δ (p.relabel j) (vertices.relabel j) (ctx.relabel j) (dom.relabel j)
      (cod.relabel j) (fn.relabel j) (arg.relabel j) := by
  constructor
  · have d := renameInto paid.valid j Δ keep
    simpa only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] using d
  · have d := renameInto paid.measured j Δ keep
    simpa only [measureRename,auxiliaryRename] using d
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
    (p vertices ctx dom cod fn arg mf ma df da bf ba fState fTerms fArgs : OTerm α)
    (paid : Inputs V TV M B TW s body Γ p vertices ctx dom cod fn arg)
    (f : MeasuredChild M s body Γ mf df bf fState fTerms fArgs fn)
    (argLocal : LocalChild V TV M (strictAuxWindow B TW) s body Γ ctx dom arg)
    (argData : AuxMeasureChild M body Γ arg ma da ba)
    (emit : Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma]))) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenCoverAuxMeasuredChildCases V TV M (strictAuxWindow B TW) s body α Γ
    ctx dom arg ma da ba _ argLocal argData
  intro β j Δ aState aTerms aArgs keep a
  rw [graphRename,auxiliaryRename]
  have paid' := moveInputs V TV M B TW s j keep paid
  have f' := moveMeasured M s j keep f
  have emit' := renameInto emit j Δ keep
  rw [programRename,binaryInputsRename] at emit'
  exact exact_OpenSelectedGrammarAuxScratchMeasured (auxSyntax V TV) M s body β Δ
    (p.relabel j) (mf.relabel j) (ma.relabel j) (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j) aState aTerms aArgs (vertices.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    f' a emit' paid'.domMember paid'.codMember paid'.valid paid'.held

theorem fromMeasured (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (p vertices ctx dom cod fn arg mf ma df da bf ba : OTerm α)
    (paid : Inputs V TV M B TW s body Γ p vertices ctx dom cod fn arg)
    (fnLocal : LocalChild V TV M (strictAuxWindow B TW) s body Γ ctx (rawCons dom cod) fn)
    (argLocal : LocalChild V TV M (strictAuxWindow B TW) s body Γ ctx dom arg)
    (fnData : AuxMeasureChild M body Γ fn mf df bf)
    (argData : AuxMeasureChild M body Γ arg ma da ba)
    (emit : Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma]))) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenCoverAuxMeasuredChildCases V TV M (strictAuxWindow B TW) s body α Γ
    ctx (rawCons dom cod) fn mf df bf _ fnLocal fnData
  intro β j Δ fState fTerms fArgs keep f
  rw [graphRename,auxiliaryRename]
  have paid' := moveInputs V TV M B TW s j keep paid
  have argLocal' := moveLocal V TV M (strictAuxWindow B TW) s j keep argLocal
  have argData' := moveChild M j Δ keep argData
  have emit' := renameInto emit j Δ keep
  rw [programRename,binaryInputsRename] at emit'
  exact atFunction V TV M B TW s (p.relabel j) (vertices.relabel j) (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    (mf.relabel j) (ma.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j)
    fState fTerms fArgs paid' f argLocal' argData' emit'

#print axioms fromMeasured

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnScopesProof
