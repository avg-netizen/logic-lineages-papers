module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (termListAtMeasure)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverCombinedRestrictedCommonCoverTapeProof
  (selectedOptionFromActualList coverFromActualGenerator)
open NumberedWindowInternalCoverCombinedRestrictedCommonCoverTargets

theorem exact_OpenCoverCommonSelectedCover : ExactOpenCoverCommonSelectedCover := by
  intro V N s body α Γ a b m goal va vb ma mb k
  apply programCases termListAtMeasure ![headsTerm s α,typesTerm s α,m] goal
  intro β j Δ vertices keep listGraph
  simp only [tripleInputsRename,headsTerm,typesTerm,numeralRename] at listGraph
  have va' := renameInto va j Δ keep
  have vb' := renameInto vb j Δ keep
  have ma' := renameInto ma j Δ keep
  have mb' := renameInto mb j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at va' vb'
  simp only [unaryRename] at ma' mb'
  have shared := selectedOptionFromActualList (headsTerm s β) (typesTerm s β) (m.relabel j) vertices listGraph
  have ca := coverFromActualGenerator V N s vertices (m.relabel j) (a.relabel j) va' ma' shared
  have cb := coverFromActualGenerator V N s vertices (m.relabel j) (b.relabel j) vb' mb' shared
  exact k β j Δ vertices keep ca cb

theorem exact_OpenCoverCombinedRestrictedCommonCover : ExactOpenCoverCombinedRestrictedCommonCover := by
  intro V TV M M0 B T s body α Γ a b m goal P va vb ma mb k
  exact exact_OpenCoverCommonSelectedCover P.V (selectedMeasure P.R) s body α Γ a b m goal va vb ma mb k

#print axioms exact_OpenCoverCommonSelectedCover
#print axioms exact_OpenCoverCombinedRestrictedCommonCover
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverProof
