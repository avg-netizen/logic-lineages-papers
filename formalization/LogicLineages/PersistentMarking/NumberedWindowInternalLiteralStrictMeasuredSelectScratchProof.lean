module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedScratchAuxiliaryWindowProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxiliaryWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredSelectScratchProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax auxSyntaxChildren)
open NumberedWindowInternalCoverAuxSyntaxOpenIntroProof (exact_OpenCoverAuxSyntaxIntro)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (measureRename pairRename)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (MeasuredChild chosenMeasure)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredProof (exact_OpenSelectedGrammarAuxScratchMeasured)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof (exact_OpenUnrestrictedWindowReports)
open NumberedWindowInternalMeasuredUnrestrictedAuxiliaryWindowProof (exact_OpenMeasuredUnrestrictedAuxiliaryWindow)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

open NumberedWindowInternalLiteralStrictMeasuredScratchProof
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalMeasuredUnrestrictedSelectedScratchAuxiliaryWindowProof (moveMeasuredChild)

/-- The actual original selected grammar transports both genuine child
occurrences, so no parent scratch or own-membership premise remains. -/
theorem exact_OpenStrictMeasuredSelectedScratch
    (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg p mf ma df bf da ba fState fTerms fArgs aState aTerms aArgs : OTerm α) :
    let baseW := strictAuxWindow base T
    let Va := unitAuxSyntax V TV
    let C := measuredStrictCover V TV baseM
    let W := measuredStrictWindow s base T V TV baseM
    let q := auxiliaryTerm dom cod fn arg
    Nonempty (Derivation B Γ (windowAt W ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation B Γ (windowAt W ctx dom arg)) →
    MeasuredChild baseM s B Γ mf df bf fState fTerms fArgs fn →
    MeasuredChild baseM s B Γ ma da ba aState aTerms aArgs arg →
    Nonempty (Derivation B Γ (programGraph chosenCombine p ![mf,ma])) →
    Nonempty (Derivation B Γ (unary T (suc z) dom ⊓ unary T (suc z) cod)) →
    Nonempty (Derivation B Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation B Γ (memberGraph (typesTerm s α) dom)) →
    Nonempty (Derivation B Γ (memberGraph (typesTerm s α) cod)) →
    Nonempty (Derivation B Γ (windowAt W ctx cod q)) := by
  intro baseW Va C W q fnHeld argHeld f a combine t tv hd hc
  apply programCases (scratchVertices C s) (![q] : Fin 1 → OTerm α) _
  intro β j Δ vertices keep scratch
  rw [windowRename,auxiliaryRename]
  rw [unaryInputsRename] at scratch
  simp only [q,auxiliaryRename] at scratch
  have fHeld := renameInto fnHeld j Δ keep
  have aHeld := renameInto argHeld j Δ keep
  simp only [windowRename,rawConsRename] at fHeld aHeld
  have f' := moveMeasuredChild baseM s mf df bf fState fTerms fArgs fn j keep f
  have a' := moveMeasuredChild baseM s ma da ba aState aTerms aArgs arg j keep a
  have combined := renameInto combine j Δ keep
  simp only [programRename,binaryInputsRename] at combined
  have t' := renameInto t j Δ keep
  have tv' := renameInto tv j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at t' tv'
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  simp only [graphRename,typesTerm,numeralRename] at hd' hc'
  exact exact_OpenStrictMeasuredAtScratch s base T V TV baseM (ctx.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) (p.relabel j) (mf.relabel j) (ma.relabel j)
    (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j)
    (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j) vertices
    fHeld aHeld f' a' combined t' tv' hd' hc' scratch

#print axioms exact_OpenStrictMeasuredSelectedScratch
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredSelectScratchProof
