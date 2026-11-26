module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredSelectScratchProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof

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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredFormationInputsProof
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

open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof (Inputs moveInputs)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictWindow)
open NumberedWindowInternalLiteralStrictMeasuredSelectScratchProof (exact_OpenStrictMeasuredSelectedScratch)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Open the actual chosen combine on the exact child values; no external
combine result or parent output is needed once the children's scopes are held. -/
theorem exact_OpenStrictMeasuredFormationFromScopes (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg mf df bf fState fTerms fArgs ma da ba aState aTerms aArgs : OTerm α) :
    let W := measuredStrictWindow s base T V TV baseM
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
  exact exact_OpenStrictMeasuredSelectedScratch s base T V TV baseM
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) p
    (mf.relabel j) (ma.relabel j) (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j)
    (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
    h.function h.argument f' a' combined h.intrinsicTypes h.syntaxTypes h.domainMember h.codomainMember

#print axioms exact_OpenStrictMeasuredFormationFromScopes
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredFormationInputsProof
