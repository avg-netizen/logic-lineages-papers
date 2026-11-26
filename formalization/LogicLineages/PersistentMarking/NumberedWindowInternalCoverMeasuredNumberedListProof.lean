module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredNumberedListBoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionPlacementProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredNumberedListProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (renameRow)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentGrammarInductionBindingProof (argumentExistsRename)
open NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof (consumeArgument)
open NumberedWindowInternalCoverArgumentGrammarInductionPlacementProof (moveArgumentHit)
open NumberedWindowInternalCoverMeasuredNumberedListBoundsProof (actualMeasuredNumberedLists)
open NumberedWindowInternalCoverGuardedNumberedListTargets

theorem exact_OpenCoverMeasuredNumberedListScratch : ExactOpenCoverMeasuredNumberedListScratch := by
  intro V TV M F B T s body α Γ h ty k l r p vertices ctx result row left right
  let P := lexicalFittedPrograms s V TV M (argumentMeasure F) B T
  let Q := memberGraph vertices (numberedTerm h ty k l r)
  apply consumeArgument F s l Q left
  intro β j Δ ml dl wl ls lt la keep measureL pairL hitL
  have actualR := renameInto right j Δ keep
  rw [argumentExistsRename] at actualR
  apply consumeArgument F s (r.relabel j) (Q.relabel j) actualR
  intro γ g Ξ mr dr wr rs rt ra retain measureR pairR hitR
  let m := g ∘ j
  have both := keepThrough j g keep retain
  have row' := renameRow P s m both row
  rw [numberedRename] at row'
  have measure := renameInto measureL g Ξ retain
  simp only [unaryRename,Term.relabel_relabel] at measure
  have pair := renameInto pairL g Ξ retain
  rw [pairRename] at pair
  have lHit := moveArgumentHit s dl wl ls lt la (l.relabel j) g Ξ retain hitL
  simp only [Term.relabel_relabel] at lHit measureR hitR
  rw [formulaRelabelComposition j g Q]
  simp only [Q,graphRename,numberedRename]
  exact actualMeasuredNumberedLists V TV M F B T s (h.relabel m) (ty.relabel m) (k.relabel m)
    (l.relabel m) (r.relabel m) (p.relabel m) (vertices.relabel m) (ctx.relabel m) (result.relabel m)
    (ml.relabel g) (dl.relabel g) (wl.relabel g) (ls.relabel g) (lt.relabel g) (la.relabel g)
    mr dr wr rs rt ra row' measure pair lHit measureR pairR hitR

#print axioms exact_OpenCoverMeasuredNumberedListScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredNumberedListProof
