module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowTargets
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

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
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
open NumberedWindowInternalCoverHeadWindowTargets

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

theorem exact_OpenCoverHeadShape : ExactOpenCoverHeadShape := by
  intro b body α Γ h tail len
  let tag := headTag b
  let val := numeral (α := α) tag
  let raw := headKey b h tail
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) val (packedBody (h::tail))
  have head : Nonempty (Derivation body Γ (unary cellHead val raw)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have below6 : tag < 6 := by cases b <;> decide
  have above3 : 3 < tag := by cases b <;> decide
  have above0 : 0 < tag := by cases b <;> decide
  have above1 : 1 < tag := by cases b <;> decide
  have noAux := rejectHeader 6 4 raw val head (rejectForwardOrder val (numeral 6) (ltTag tag 6 below6))
  have noType := rejectHeader 3 1 raw val head (rejectBackwardOrder val (numeral 3) (ltTag 3 tag above3))
  have noFree := rejectHeader 0 2 raw val head (rejectBackwardOrder val (numeral 0) (ltTag 0 tag above0))
  have noBound := rejectHeader 1 2 raw val head (rejectBackwardOrder val (numeral 1) (ltTag 1 tag above1))
  have code : Nonempty (Derivation body Γ (unary (literal 1 tag) val raw)) := literalGraph tag ![raw]
  have yes := packedNode (literal 1 tag) val (h::tail) code
  have accepted : Nonempty (Derivation body Γ (unary (header tag (headArity b)) (suc z) raw)) := by
    change Nonempty (Derivation body Γ (unary (nodeGood (literal 1 tag) (headArity b)) (suc z) raw))
    rw [← len]
    exact yes.1
  refine ⟨noAux,noType,noFree,noBound,accepted,yes.2.1,?_⟩
  intro numbered
  have above4 : 4 < tag := by simpa only [tag,numbered] using (show (4 : Nat) < headTag true by decide)
  exact rejectHeader 4 2 raw val head (rejectBackwardOrder val (numeral 4) (ltTag 4 tag above4))

#print axioms exact_OpenCoverHeadShape

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
