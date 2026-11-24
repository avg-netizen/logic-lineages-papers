module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedScratchAuxiliaryWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (MeasuredChild chosenMeasure)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalMeasuredUnrestrictedSelectedScratchAuxiliaryWindowProof
  (moveMeasuredChild exact_OpenUnrestrictedSelectedScratchAuxiliaryWindow)

abbrev selectedBase (base : Program 2) (T : Program 1) : Program 3 :=
  intrinsicQuery (selectedIntrinsic (windowUpdate base T))

abbrev selectedWindow (s : Settings) (base : Program 2) (T V TV baseM : Program 1) : Program 3 :=
  let Va := auxSyntax V TV
  window (selectedCover Va (chosenMeasure baseM)) s (selectedBase base T) Va

/-- Genuine child windows and three independent sources of type information.
This package asserts no grammar scope or parent condition. -/
structure Inputs (s : Settings) (W : Program 3) (T TV : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ctx dom cod fn arg : OTerm α) : Prop where
  function : Nonempty (Derivation body Γ (windowAt W ctx (rawCons dom cod) fn))
  argument : Nonempty (Derivation body Γ (windowAt W ctx dom arg))
  intrinsicTypes : Nonempty (Derivation body Γ (unary T (suc z) dom ⊓ unary T (suc z) cod))
  syntaxTypes : Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod))
  domainMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom))
  codomainMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod))

theorem moveInputs {B : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}
    (s : Settings) (W : Program 3) (T TV : Program 1) (ctx dom cod fn arg : OTerm α)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (held : Inputs s W T TV B Γ ctx dom cod fn arg) :
    Inputs s W T TV B Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [windowRename,rawConsRename] using renameInto held.function j Δ keep
  · simpa only [windowRename] using renameInto held.argument j Δ keep
  · simpa only [conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto held.intrinsicTypes j Δ keep
  · simpa only [conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto held.syntaxTypes j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto held.domainMember j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto held.codomainMember j Δ keep

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Open the actual chosen combine on the exact child values; no external
combine result or parent output is needed once the children's scopes are held. -/
theorem exact_OpenSelectedFormationFromScopes (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg mf df bf fState fTerms fArgs ma da ba aState aTerms aArgs : OTerm α) :
    let W := selectedWindow s base T V TV baseM
    Inputs s W T TV B Γ ctx dom cod fn arg →
    MeasuredChild baseM s B Γ mf df bf fState fTerms fArgs fn →
    MeasuredChild baseM s B Γ ma da ba aState aTerms aArgs arg →
    Nonempty (Derivation B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg))) := by
  intro W held f a
  apply programCases chosenCombine (![mf,ma] : Fin 2 → OTerm α) _
  intro β j Δ p keep combined
  rw [windowRename,auxiliaryRename]
  rw [binaryInputsRename] at combined
  have h := moveInputs s W T TV ctx dom cod fn arg j keep held
  have f' := moveMeasuredChild baseM s mf df bf fState fTerms fArgs fn j keep f
  have a' := moveMeasuredChild baseM s ma da ba aState aTerms aArgs arg j keep a
  exact exact_OpenUnrestrictedSelectedScratchAuxiliaryWindow s base T V TV baseM
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) p
    (mf.relabel j) (ma.relabel j) (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j)
    (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
    h.function h.argument f' a' combined h.intrinsicTypes h.syntaxTypes h.domainMember h.codomainMember

#print axioms moveInputs
#print axioms exact_OpenSelectedFormationFromScopes
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof
