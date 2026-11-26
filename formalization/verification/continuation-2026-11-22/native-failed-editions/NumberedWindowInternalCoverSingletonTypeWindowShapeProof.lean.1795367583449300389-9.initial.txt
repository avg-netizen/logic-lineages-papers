module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureDispatchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowShapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction constantZero branch)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue valueUnique)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (trans congSuc addZero addSucc sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelope (applyUnary exactBody field)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellGood cellTail)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (certain shapeCheck earlierAt)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverSharedRecursionTargets (lambdaDispatch)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest leafIntrinsicBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (grammarGuard namedGrammarAt namedGrammarBase)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalGuard lexicalBoundBase)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSingletonTypeWindowTargets

open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphProof (zeroTestAtZero)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (makeUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverSingletonTypeArgumentTargets (singletonTypeGuard singletonTypeKey)
open NumberedWindowInternalCoverTypeLeafMeasureDispatchProof (exact_OpenCoverTypeLeafMeasureDispatch)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def addLiteral (a k : Nat) : Derivation body Γ
    (eqn (OrdinaryArithmetic.addTerm (numeral a) (numeral k)) (numeral (a+k))) := by
  induction k with
  | zero => exact addZero (numeral a)
  | succ k ih => exact trans (addSucc (numeral a) (numeral k)) (congSuc ih)

private theorem ltLiteral (a gap : Nat) : Nonempty (Derivation body Γ
    (ltF (numeral a) (numeral (a+gap+1)))) := by
  apply actualOriginalOrderIntroduction body α Γ (numeral a) (numeral (a+gap+1)) (numeral gap)
  rw [onEquality]
  exact ⟨addLiteral a (gap+1)⟩

private theorem leftZero {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (zero : Nonempty (Derivation body Γ (programGraph p z xs))) :
    Nonempty (Derivation body Γ (programGraph (conjunction p q) z xs)) := by
  let F := programGraph (conjunction p q) (suc z) xs
  apply conjunctionReject p q xs
  obtain ⟨both⟩ := conjunctionRecover p q xs (body := body) (Gamma := F :: Γ) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨bad⟩ := valueUnique p (suc z) z xs ⟨Derivation.conjunctionLeft both⟩ (withHyp zero F)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply bad)⟩

private theorem rightZero {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (zero : Nonempty (Derivation body Γ (programGraph q z xs))) :
    Nonempty (Derivation body Γ (programGraph (conjunction p q) z xs)) := by
  let F := programGraph (conjunction p q) (suc z) xs
  apply conjunctionReject p q xs
  obtain ⟨both⟩ := conjunctionRecover p q xs (body := body) (Gamma := F :: Γ) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨bad⟩ := valueUnique q (suc z) z xs ⟨Derivation.conjunctionRight both⟩ (withHyp zero F)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply bad)⟩

private theorem rejectHeader (tag arity : Nat) (raw h : OTerm α)
    (head : Nonempty (Derivation body Γ (unary cellHead h raw)))
    (different : Nonempty (Derivation body Γ (programGraph equalityTest z ![h,numeral tag]))) :
    Nonempty (Derivation body Γ (unary (header tag arity) z raw)) := by
  let t := literal 1 tag
  let E : Program 1 := .composition equalityTest ![cellHead,t]
  let A := applyUnary (exactBody arity) cellTail
  have rejected : Nonempty (Derivation body Γ (unary E z raw)) := by
    apply compositionValue equalityTest ![cellHead,t] z ![raw] ![h,numeral tag] different
    intro j
    exact Fin.cases head (Fin.cases (literalGraph tag ![raw]) (fun l => Fin.elim0 l)) j
  exact rightZero cellGood (conjunction E A) ![raw] (leftZero E A ![raw] rejected)

private theorem ltTag (k n : Nat) (hk : k < n) :
    Nonempty (Derivation body Γ (ltF (numeral k) (numeral n))) := by
  have he : k + (n-k-1) + 1 = n := by omega
  simpa only [he] using (ltLiteral (body := body) (Γ := Γ) k (n-k-1))

structure OrdinarySingletonShape (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (h ty : OTerm α) : Prop where
  lambdaZero : Nonempty (Derivation body Γ (unary (header 2 2) z (ordinaryKey h (singletonTypeKey ty))))
  numberedZero : Nonempty (Derivation body Γ (unary (header 5 5) z (ordinaryKey h (singletonTypeKey ty))))
  guard : Nonempty (Derivation body Γ (unary ordinarySingletonGuard (suc z) (ordinaryKey h (singletonTypeKey ty))))
  storedType : Nonempty (Derivation body Γ (unary singletonTypeSelector ty (ordinaryKey h (singletonTypeKey ty))))

private theorem actualSingleton (ty : OTerm α) :
    Nonempty (Derivation body Γ (unary singletonTypeGuard (suc z) (singletonTypeKey ty))) := by
  let q := typeLeafTerm ty
  let key := singletonTypeKey ty
  let Z := LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.zeroTest
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) q z
  have head := (exact_OpenCoverTypeLeafMeasureDispatch body α Γ ty z).2.2
  have hh := makeUnary (header 3 1) cellHead (suc z) key q head
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have tail : Nonempty (Derivation body Γ (unary Z (suc z) (z : OTerm α))) :=
    zeroTestAtZero z ⟨refl z⟩
  have tt := makeUnary Z cellTail (suc z) key z tail
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩
  exact conjunctionAccept cellGood (conjunction (applyUnary (header 3 1) cellHead) (applyUnary Z cellTail))
    ![key] ⟨Derivation.conjunctionLeft cell⟩
    (conjunctionAccept (applyUnary (header 3 1) cellHead) (applyUnary Z cellTail) ![key] hh tt)

theorem actualOrdinarySingletonShape (h ty : OTerm α) : OrdinarySingletonShape body Γ h ty := by
  let q := typeLeafTerm ty
  let key := singletonTypeKey ty
  let raw := ordinaryKey h key
  let four : OTerm α := numeral 4
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) four (packedBody [h,key])
  have head : Nonempty (Derivation body Γ (unary cellHead four raw)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have noLambda := rejectHeader 2 2 raw four head
    (rejectBackwardOrder four (numeral 2) (ltTag 2 4 (by decide)))
  have noNum := rejectHeader 5 5 raw four head
    (rejectForwardOrder four (numeral 5) (ltTag 4 5 (by decide)))
  have top := packedNode (literal 1 4) four [h,key] (literalGraph 4 ![raw])
  have arg := top.2.2.1
  have child := makeUnary singletonTypeGuard (field 1) (suc z) raw key (actualSingleton ty) arg
  have guard := conjunctionAccept (header 4 2) (applyUnary singletonTypeGuard (field 1)) ![raw] top.1 child
  obtain ⟨argCell⟩ := canonicalCell (body := body) (Γ := Γ) q z
  have childHead := makeUnary cellHead (field 1) q raw key
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight argCell)⟩ arg
  have childType :=
    (packedNode (literal 1 3) (numeral 3) [ty] (literalGraph 3 ![q])).2.1
  exact ⟨noLambda,noNum,guard,
    makeUnary (field 0) (applyUnary cellHead (field 1)) ty raw q childType childHead⟩

#print axioms actualOrdinarySingletonShape

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowShapeProof
