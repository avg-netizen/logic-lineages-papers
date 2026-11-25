module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTickOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFrameZeroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalRecursionGraphExtensionSupportProof (successorOrder)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (nodeGood applyUnary exactBody)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawRunRootTapeProof (rejectLeft rejectRight)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm)
open NumberedWindowInternalLiteralNeutralAtomProof (zeroBelowSuccessor)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nodeTagReject (tag limit : Nat) (actual : OTerm α) (fields : List (OTerm α))
    (different : D B Γ (programGraph equalityTest z ![actual,numeral tag])) :
    D B Γ (unary (nodeGood (literal 1 tag) limit) z (rawCons actual (packedBody fields))) := by
  let code := rawCons actual (packedBody fields)
  let P : Program 1 := .composition equalityTest ![cellHead,literal 1 tag]
  let Q := applyUnary (exactBody limit) cellTail
  obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Γ) actual (packedBody fields)
  have shape : D B Γ (unary cellGood (suc z) code) := ⟨Derivation.conjunctionLeft cell⟩
  have tagField : D B Γ (unary cellHead actual code) := ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have no : D B Γ (unary P z code) := by
    apply compositionValue equalityTest ![cellHead,literal 1 tag] z ![code] ![actual,numeral tag] different
    exact fun k => Fin.cases tagField (Fin.cases (literalGraph tag ![code]) (fun e => Fin.elim0 e)) k
  exact rejectRight cellGood (conjunction P Q) ![code] shape (rejectLeft P Q ![code] no)

theorem exact_OpenLiteralAtomicAuxReject (t n : OTerm α) :
    D B Γ (unary termShape z (freeTerm t n)) ∧ D B Γ (unary termShape z (bottomTerm t)) := by
  have f : D B Γ (ltF (z : OTerm α) (numeral 6)) := zeroBelowSuccessor (numeral 5)
  have b : D B Γ (ltF (numeral 3 : OTerm α) (numeral 6)) :=
    successorOrder (numeral 2) (numeral 5)
      (successorOrder (numeral 1) (numeral 4)
        (successorOrder (numeral 0) (numeral 3) (zeroBelowSuccessor (numeral 2))))
  exact ⟨nodeTagReject 6 4 z [t,n] (rejectForwardOrder z (numeral 6) f),
    nodeTagReject 6 4 (numeral 3) [t] (rejectForwardOrder (numeral 3) (numeral 6) b)⟩

theorem exact_OpenLiteralBottomTests (t : OTerm α) :
    D B Γ (unary freeTest z (bottomTerm t)) ∧ D B Γ (unary bottomTest (suc z) (bottomTerm t)) := by
  have less : D B Γ (ltF (z : OTerm α) (numeral 3)) := zeroBelowSuccessor (numeral 2)
  have notFree := nodeTagReject 0 2 (numeral 3) [t] (rejectBackwardOrder (numeral 3) z less)
  have tag : D B Γ (unary (literal 1 3) (numeral 3) (bottomTerm t)) := literalGraph 3 ![bottomTerm t]
  exact ⟨notFree,(packedNode (body := B) (Γ := Γ) (literal 1 3) (numeral 3) [t] tag).1⟩

private theorem rightZero {m : Nat} (p q : Program m) (xs : Fin m → OTerm α)
    (zero : D B Γ (programGraph q z xs)) :
    D B Γ (programGraph (conjunction p q) z xs) := by
  let A := programGraph (conjunction p q) (suc z) xs
  have no : D B Γ A.not := by
    have hit : D B (A :: Γ) A := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨pair⟩ := conjunctionRecover p q xs hit
    obtain ⟨rejected⟩ := zero
    obtain ⟨impossible⟩ := valueUnique q (suc z) z xs ⟨Derivation.conjunctionRight pair⟩ ⟨addHyp rejected _⟩
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply impossible)⟩
  exact conjunctionReject p q xs no

/-- The early dedicated tag-five fast path also really rejects a raw
source rejected by the auxiliary shape test. Checking only the older
fallback would not suffice for the physical tick. -/
theorem exact_OpenLiteralAtomicNoFunctionFrame (q w r : OTerm α)
    (notAux : D B Γ (unary termShape z q)) :
    D B Γ (programGraph chosenFrame z ![q,w,r]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let tail := conjunction (onRaw termShape 2)
    (conjunction (sameSlot 0) (conjunction (sameSlot 1) (sameSlot 3)))
  have stopped := rejectLeft (onRaw termShape 0) tail xs (onTape termShape 0 z xs notAux)
  have guard : D B Γ (programGraph frameGood z xs) :=
    rightZero (onRaw witnessShape 1) (conjunction (onRaw termShape 0) tail) xs stopped
  exact zeroBranchIntro frameGood (constantZero 3) emitFrame z xs guard (constantZeroValue xs)

#print axioms exact_OpenLiteralAtomicAuxReject
#print axioms exact_OpenLiteralBottomTests
#print axioms exact_OpenLiteralAtomicNoFunctionFrame
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFrameZeroProof
