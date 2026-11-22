module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryEmptyArgsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs ParentRow)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarNullaryEmptyArgsProof (exact_OpenSelectedGrammarEmptyArgs)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets (NumberedOwnInputs)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnScratchProof (exact_OpenSelectedGrammarNumberedScratch)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase)
open NumberedWindowInternalCoverNumberedTypeWindowSelectedProof (exact_OpenCoverNumberedTypeWindow)
open NumberedWindowInternalCoverHeadWindowSelectedProof (exact_OpenCoverHeadFittedWindow)
open NumberedWindowInternalCoverNumberedMeasureCombineTargets (NumberedJoinBounds)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasuredPrograms)
open NumberedWindowInternalCoverNumberedEmptyMeasureProof (exact_OpenCoverNumberedEmptyMeasure)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough moveParentPair moveWeak moveStoredK)
open NumberedWindowInternalCoverNumberedEmptyTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The two complete original observation tapes, one at each actual empty
argument position, are consumed before staging the physical numbered parent. -/
private theorem emptyAtRows (P : Programs) (s : Settings) (h ty k p vertices ctx result : OTerm α)
    (row : ParentRow P s body Γ (emptyNumberedKey h ty k) p vertices ctx result)
    (heads : Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h)))
    (types : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)))
    (paid : NumberedJoinBounds body Γ p k z z z z k) :
    Nonempty (Derivation body Γ (memberGraph vertices (emptyNumberedKey h ty k))) := by
  let Q := memberGraph vertices (emptyNumberedKey h ty k)
  apply observationCases z (headsTerm s α) (typesTerm s α) z Q
  intro β j Δ ls lt la keep left
  apply observationCases z (headsTerm s β) (typesTerm s β) z (Q.relabel j)
  intro γ g Ξ rs rt ra retain right
  let q := g ∘ j
  have both := keepThrough j g keep retain
  have a := renameInto left g Ξ retain
  simp only [observedRename,zRelabel,headsTerm,typesTerm,numeralRename] at a right
  have leftHit := exact_OpenSelectedGrammarEmptyArgs body γ Ξ z (headsTerm s γ) (typesTerm s γ) z
    (ls.relabel g) (lt.relabel g) (la.relabel g) a
  have rightHit := exact_OpenSelectedGrammarEmptyArgs body γ Ξ z (headsTerm s γ) (typesTerm s γ) z
    rs rt ra right
  have hh := renameInto heads q Ξ both
  simp only [graphRename,headsTerm,numeralRename] at hh
  have kt := moveStoredK s q both ty types
  have pp := moveParentPair q both p (add z z) k paid.parent
  have dl := moveWeak q both z (add z z) paid.leftDepth
  have dr := moveWeak q both z (add z z) paid.rightDepth
  have wl := moveWeak q both z k paid.leftWidth
  have wr := moveWeak q both z k paid.rightWidth
  have id := moveWeak q both k k paid.storedNumeral
  simp only [addRelabel,zRelabel] at pp dl dr wl wr
  have parent := moveParent P.V P.R s q both row.parent
  simp only [emptyNumberedKey,numberedRename,zRelabel] at parent
  let d := add (z : OTerm γ) z
  let width := k.relabel q
  have input : NumberedOwnInputs P.V (selectedMeasure P.R) s body Ξ (p.relabel q)
      d width z z (ls.relabel g) (lt.relabel g) (la.relabel g) z z rs rt ra
      (h.relabel q) (ty.relabel q) width z z :=
    ⟨⟨a,leftHit,dl,wl⟩,⟨right,rightHit,dr,wr⟩,hh,kt,id,parent.valid,parent.measured,pp⟩
  rw [formulaRelabelComposition j g Q]
  simp only [Q,graphRename,emptyNumberedKey,numberedRename,zRelabel]
  exact exact_OpenSelectedGrammarNumberedScratch P.V (selectedMeasure P.R) s body γ Ξ (p.relabel q) d width
    z z (ls.relabel g) (lt.relabel g) (la.relabel g) z z rs rt ra
    (vertices.relabel q) (h.relabel q) (ty.relabel q) width z z input parent.held

theorem exact_OpenCoverNumberedEmptyFittedScratch : ExactOpenCoverNumberedEmptyFittedScratch := by
  intro V TV M A B T s body α Γ h ty k p vertices ctx result row
  let P := numberedMeasuredPrograms s V TV M A B T
  have heads := exact_OpenCoverHeadFittedWindow true s (numberedTypeBase s B) T
    body α Γ ctx h result [ty,k,z,z] rfl row.typed
  have types := exact_OpenCoverNumberedTypeWindow s B T body α Γ ctx h ty k z z result row.typed
  have measured := exact_OpenCoverNumberedEmptyMeasure M A body α Γ h ty k p row.parent.measured
  exact emptyAtRows P s h ty k p vertices ctx result row heads types measured

#print axioms exact_OpenCoverNumberedEmptyFittedScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyScratchProof
