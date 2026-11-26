module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedCutProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalAcceptance (branch conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue valueUnique)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectBackwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF addRelabel)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (trans congSuc addZero addSucc sucNeZeroApply)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody packedBodyRename unaryRename)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate certain shapeCheck earlierAt measureAt)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasureUpdate lambdaBump)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypePrior)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeadWindowTargets (headPrior headTag)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (leafMeasureBase leafPair10)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedMeasureBase namedMeasurePair)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasureUpdate lambdaDispatch)
open NumberedWindowInternalCoverSharedMemoTargets (ObservedStep)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryMeasureBase ordinarySelectedBump)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (h ty k l r : OTerm α) (j : α → β) :
    (numberedTypePrior h ty k l r).relabel j =
      numberedTypePrior (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [numberedTypePrior,headPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem twoBelowFive : Nonempty (Derivation body Γ
    (ltF (numeral (α := α) 2) (numeral 5))) := by
  let two : OTerm α := numeral 2
  let one : OTerm α := numeral 1
  apply actualOriginalOrderIntroduction body α Γ two (numeral 5) two
  rw [onEquality]
  exact ⟨trans (addSucc two two) (congSuc
    (trans (addSucc two one) (congSuc (trans (addSucc two z) (congSuc (addZero two))))))⟩

private theorem leftZero {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (zero : Nonempty (Derivation body Γ (programGraph p z xs))) :
    Nonempty (Derivation body Γ (programGraph (conjunction p q) z xs)) := by
  let F := programGraph (conjunction p q) (suc z) xs
  apply conjunctionReject p q xs
  obtain ⟨both⟩ := conjunctionRecover p q xs (body := body) (Gamma := F :: Γ) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨bad⟩ := valueUnique p (suc z) z xs ⟨Derivation.conjunctionLeft both⟩ (withHyp zero F)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply bad)⟩

private theorem fromRow (M A : Program 1) (h ty k l r old p : OTerm α)
    (row : ObservedStep (sharedMeasureUpdate (leafMeasureBase (namedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A))))
      body Γ (numberedTypePrior h ty k l r) old p) :
    Nonempty (Derivation body Γ
      (unary (numberedMeasureApply A) p (numberedTerm h ty k l r))) := by
  let U := numberedMeasureBase M A
  let L := ordinaryMeasureBase U A
  let N := namedMeasureBase L
  let B := leafMeasureBase N
  let raw := numberedTerm h ty k l r
  let prior := numberedTypePrior h ty k l r
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  have shape := exact_OpenCoverHeadShape true body α Γ h [ty,k,l,r] rfl
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) (numeral 5) (packedBody [h,ty,k,l,r])
  have head : Nonempty (Derivation body Γ (unary cellHead (numeral 5) raw)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have read := unaryGraph cellHead currentKey (numeral 5) raw xs head key
  have notLambda : Nonempty (Derivation body Γ (programGraph lambdaDispatch z xs)) :=
    binaryGraph equalityTest (unaryAfter cellHead currentKey) (literal 4 2) z
      (numeral 5) (numeral 2) xs (rejectBackwardOrder (numeral 5) (numeral 2) twoBelowFive) read (literalGraph 2 xs)
  have auxShape : Nonempty (Derivation body Γ (programGraph shapeCheck z xs)) :=
    unaryGraph (header 6 4) currentKey z raw xs shape.notAux key
  have notAux : Nonempty (Derivation body Γ (programGraph certain z xs)) :=
    leftZero shapeCheck (conjunction (earlierAt 2) (earlierAt 3)) xs auxShape
  have aux := zeroBranchElim lambdaDispatch (measureUpdate B chosenCombine) (lambdaMeasureUpdate B)
    p xs notLambda row.update
  have base := zeroBranchElim certain (unaryAfter B currentKey)
    (binaryAfter chosenCombine (measureAt 2) (measureAt 3)) p xs notAux aux
  have call : Nonempty (Derivation body Γ (unary B p raw)) := by
    apply compositionRecover B (fun _ : Fin 1 => currentKey) p xs ![raw] base
    intro i
    obtain rfl := Fin.eq_zero i
    exact key
  have n := zeroBranchElim (header 3 1) N leafPair10 p ![raw] shape.notTypeLeaf call
  have bound := zeroBranchElim (header 0 2) (branch (header 1 2) L namedMeasurePair)
    namedMeasurePair p ![raw] shape.notFree n
  have ordinary := zeroBranchElim (header 1 2) L namedMeasurePair p ![raw] shape.notBound bound
  have numbered := zeroBranchElim (header 4 2) U (ordinarySelectedBump A) p ![raw]
    (shape.notOrdinary rfl) ordinary
  exact successorBranchElim (header 5 5) M (numberedMeasureApply A) p z ![raw]
    shape.accepted numbered

theorem exact_OpenCoverNumberedMeasureCut : ExactOpenCoverNumberedMeasureCut := by
  intro M A body α Γ h ty k l r p parent
  let R := sharedMeasureUpdate (leafMeasureBase (namedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A)))
  apply exact_OpenCoverSharedMemoRowCases R body α Γ (numberedTypePrior h ty k l r) p _ parent
  intro β j Δ old keep row
  simp only [unaryRename,numberedRename]
  rw [priorRename] at row
  exact fromRow M A (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) old (p.relabel j) row

#print axioms exact_OpenCoverNumberedMeasureCut

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedCutProof
