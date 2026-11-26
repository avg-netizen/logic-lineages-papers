module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
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
open NumberedWindowInternalCoverLambdaLexicalWindowTargets

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

structure LexicalLambdaShape (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (ty q : OTerm α) : Prop where
  auxZero : Nonempty (Derivation body Γ (unary termShape z (lambdaTerm ty q)))
  freeZero : Nonempty (Derivation body Γ (unary (header 0 2) z (lambdaTerm ty q)))
  boundZero : Nonempty (Derivation body Γ (unary (header 1 2) z (lambdaTerm ty q)))
  typeZero : Nonempty (Derivation body Γ (unary (header 3 1) z (lambdaTerm ty q)))
  ordinaryZero : Nonempty (Derivation body Γ (unary (header 4 2) z (lambdaTerm ty q)))
  numberedZero : Nonempty (Derivation body Γ (unary (header 5 5) z (lambdaTerm ty q)))
  lambdaYes : Nonempty (Derivation body Γ (unary (header 2 2) (suc z) (lambdaTerm ty q)))
  domainRead : Nonempty (Derivation body Γ (unary (field 0) ty (lambdaTerm ty q)))
  childRead : Nonempty (Derivation body Γ (unary (field 1) q (lambdaTerm ty q)))

theorem actualLambdaLexicalShape (ty q : OTerm α) : LexicalLambdaShape body Γ ty q := by
  let raw := lambdaTerm ty q
  let d : OTerm α := numeral 2
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) d (packedBody [ty,q])
  have head : Nonempty (Derivation body Γ (unary cellHead d raw)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have noAux := rejectHeader 6 4 raw d head (rejectForwardOrder d (numeral 6) (ltTag 2 6 (by decide)))
  have noType := rejectHeader 3 1 raw d head (rejectForwardOrder d (numeral 3) (ltTag 2 3 (by decide)))
  have noOrd := rejectHeader 4 2 raw d head (rejectForwardOrder d (numeral 4) (ltTag 2 4 (by decide)))
  have noNum := rejectHeader 5 5 raw d head (rejectForwardOrder d (numeral 5) (ltTag 2 5 (by decide)))
  have noFree := rejectHeader 0 2 raw d head (rejectBackwardOrder d (numeral 0) (ltTag 0 2 (by decide)))
  have noBound := rejectHeader 1 2 raw d head (rejectBackwardOrder d (numeral 1) (ltTag 1 2 (by decide)))
  have code : Nonempty (Derivation body Γ (unary (literal 1 2) d raw)) := literalGraph 2 ![raw]
  have yes := packedNode (literal 1 2) d [ty,q] code
  exact ⟨noAux,noFree,noBound,noType,noOrd,noNum,yes.1,yes.2.1,yes.2.2.1⟩

#print axioms actualLambdaLexicalShape

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
