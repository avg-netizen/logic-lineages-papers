module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchObservedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchInputsRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMembershipProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
open NumberedWindowInternalCoverSelectedGrammarAuxScratchObservedProof (exact_OpenSelectedGrammarAuxScratchAtObserved)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchInputsRenameProof (inputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem aligned (V Measure : Program 1) (s : Settings)
    (m d M df mf da ma fState fTerms fArgs aState aTerms aArgs
      prev prevTerms prevArgs next generated nextArgs vertices dom cod fn arg : OTerm α)
    (paid : AuxParentInputs V Measure s body Γ m d M df mf da ma
      fState fTerms fArgs aState aTerms aArgs dom cod fn arg)
    (before : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) (headsTerm s α) (typesTerm s α) M next generated nextArgs)))
    (actual : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s)
      vertices (auxiliaryTerm dom cod fn arg)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  obtain ⟨installed⟩ := exact_OpenSelectedGrammarAuxScratchAtObserved V Measure s body α Γ
    m d M df mf da ma fState fTerms fArgs aState aTerms aArgs
    prev prevTerms prevArgs next generated nextArgs dom cod fn arg paid before after
  have row := Derivation.conjunctionRight installed
  let parent := auxiliaryTerm dom cod fn arg
  let P := scratchVertices (selectedCover V Measure) s
  have same := valueUnique P generated vertices ![parent] ⟨Derivation.conjunctionLeft row⟩ actual
  exact headTransport scratchMember (suc z) generated vertices ![parent] same ⟨Derivation.conjunctionRight row⟩

private theorem withBefore (V Measure : Program 1) (s : Settings)
    (m d M df mf da ma fState fTerms fArgs aState aTerms aArgs
      prev prevTerms prevArgs vertices dom cod fn arg : OTerm α)
    (paid : AuxParentInputs V Measure s body Γ m d M df mf da ma
      fState fTerms fArgs aState aTerms aArgs dom cod fn arg)
    (before : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) M prev prevTerms prevArgs)))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s)
      vertices (auxiliaryTerm dom cod fn arg)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  apply observationCases (suc d) (headsTerm s α) (typesTerm s α) M _
  intro β j Δ next generated nextArgs keep after
  rw [graphRename,auxiliaryRename]
  simp only [headsTerm,typesTerm,numeralRename,sucRelabel] at after
  have p := inputsRename V Measure s m d M df mf da ma fState fTerms fArgs aState aTerms aArgs dom cod fn arg j keep paid
  have original := renameInto held j Δ keep
  rw [unaryRename,auxiliaryRename] at original
  have earlier := renameInto before j Δ keep
  rw [observedRename] at earlier
  simp only [headsTerm,typesTerm,numeralRename] at earlier
  exact aligned V Measure s (m.relabel j) (d.relabel j) (M.relabel j)
    (df.relabel j) (mf.relabel j) (da.relabel j) (ma.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j) (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
    (prev.relabel j) (prevTerms.relabel j) (prevArgs.relabel j) next generated nextArgs
    (vertices.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) p earlier after original

theorem exact_OpenSelectedGrammarAuxScratchMembership : ExactOpenSelectedGrammarAuxScratchMembership := by
  intro V Measure s body α Γ m d M df mf da ma fState fTerms fArgs aState aTerms aArgs
    vertices dom cod fn arg C parent paid held
  apply observationCases d (headsTerm s α) (typesTerm s α) M _
  intro β j Δ prev prevTerms prevArgs keep before
  rw [graphRename,auxiliaryRename]
  simp only [headsTerm,typesTerm,numeralRename] at before
  have p := inputsRename V Measure s m d M df mf da ma fState fTerms fArgs aState aTerms aArgs dom cod fn arg j keep paid
  have original := renameInto held j Δ keep
  rw [unaryRename,auxiliaryRename] at original
  exact withBefore V Measure s (m.relabel j) (d.relabel j) (M.relabel j)
    (df.relabel j) (mf.relabel j) (da.relabel j) (ma.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j) (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
    prev prevTerms prevArgs (vertices.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    p before original

#print axioms exact_OpenSelectedGrammarAuxScratchMembership

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMembershipProof
