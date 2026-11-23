module
public import LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankOpenZeroProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue acceptOfLess)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck childAt earlierAt measureAt)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection bothChildBounds nodeReports)
open NumberedWindowInternalStrictAuxWindowThinTableProof (earlierValue)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalTransparentAuxRankTargets

attribute [local irreducible] programGraph

private theorem rowZero (g : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg old : OTerm α)
    (child : Nonempty (Derivation body Γ (unary (auxRank g) z fn)))
    (table : Nonempty (Derivation body Γ (tableAt (rankUpdate g) old
      (memoPrior dom cod fn arg)))) :
    Nonempty (Derivation body Γ (programGraph (rankUpdate g) z ![memoPrior dom cod fn arg,old,z,z])) := by
  let R := rankUpdate g
  let prior := memoPrior dom cod fn arg
  let parent := auxiliaryTerm dom cod fn arg
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  have fields := nodeReports (body := body) (Γ := Γ) dom cod fn arg old
  have smaller := (bothChildBounds (body := body) (Γ := Γ) dom cod fn arg).1
  have fnEarlier := binaryGraph ltTest (childAt 2) currentKey (suc z) fn parent xs
    (acceptOfLess fn parent smaller) fields.fnField fields.key
  have admitted : Nonempty (Derivation body Γ (programGraph rankGuard (suc z) xs)) :=
    conjunctionAccept shapeCheck (earlierAt 2) xs fields.shape fnEarlier
  have atFn := earlierValue R 2 fn z prior old z fields.fnField smaller
    ((projection R z fn).mp child) table
  have zeroResult : Nonempty (Derivation body Γ (programGraph rankAtFn z xs)) :=
    zeroBranchIntro (measureAt 2) (constantZero 4) (unaryAfter .succ (measureAt 2))
      z xs atFn (zeroConstantValue xs)
  exact successorBranchIntro rankGuard (unaryAfter g currentKey) rankAtFn z z xs admitted zeroResult

/-- Same-body rank-zero introduction builds the actual memoized report on
the genuine auxiliary parent. No right child rank and no open report of
the opaque fallback g are antecedents. -/
theorem exact_OpenTransparentAuxRankZeroIntro
    (g : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg : OTerm α)
    (child : Nonempty (Derivation body Γ (unary (auxRank g) z fn))) :
    Nonempty (Derivation body Γ (unary (auxRank g) z (auxiliaryTerm dom cod fn arg))) := by
  let R : Program 4 := rankUpdate g
  let Goal : Formula α := unary (auxRank g) z (auxiliaryTerm dom cod fn arg)
  apply programCases (scratchTable (constantZero 2) R) ![memoPrior dom cod fn arg,z,z] Goal
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  let d := dom.relabel j
  let c := cod.relabel j
  let f := fn.relabel j
  let a := arg.relabel j
  have child' := renameInto child j Δ keep
  simp only [unaryRename,zRelabel] at child'
  have row := rowZero g body β Δ d c f a old child' table
  have read := exact_OpenSelectedMemoSuccessor R body β Δ z (memoPrior d c f a) old table row
  change Nonempty (Derivation body Δ ((unary (auxRank g) z (auxiliaryTerm dom cod fn arg)).relabel j))
  simp only [unaryRename,zRelabel,auxiliaryRename]
  exact (projection R z (auxiliaryTerm d c f a)).mpr read

#print axioms exact_OpenTransparentAuxRankZeroIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankOpenZeroProof
