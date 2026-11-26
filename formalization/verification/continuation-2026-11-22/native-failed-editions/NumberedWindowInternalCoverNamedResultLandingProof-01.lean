module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicBaseOpenProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultLandingProof
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
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverNamedLeafIntrinsicBaseOpenProof (exact_OpenNamedGrammarGuardSelected)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest leafIntrinsicBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (grammarGuard namedGrammarAt namedGrammarBase)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalGuard lexicalBoundBase)
open NumberedWindowInternalCoverNamedResultTargets

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

theorem actual_FreeKeyRejectsBoundHeader (ty i : OTerm α) :
    Nonempty (Derivation body Γ (unary (header 1 2) z (namedTerm 0 ty i))) := by
  let raw := namedTerm 0 ty i
  obtain ⟨report⟩ := canonicalCell (body := body) (Γ := Γ) (numeral 0) (packedBody [ty,i])
  have head : Nonempty (Derivation body Γ (unary cellHead (numeral 0) raw)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight report)⟩
  exact rejectHeader 1 2 raw (numeral 0) head (rejectForwardOrder (numeral 0) (numeral 1) (ltLiteral 0 0))

private theorem liftReport (P : Program 1) (ctx raw out : OTerm α)
    (observed : Nonempty (Derivation body Γ (unary P out raw))) :
    Nonempty (Derivation body Γ (programGraph (onRaw P) out ![ctx,raw])) := by
  apply compositionValue P (fun _ : Fin 1 => Program.projection 1) out ![ctx,raw] ![raw] observed
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue 1 ![ctx,raw]

private theorem requirePositive (P C : Program 2) (r : OTerm α) (xs : Fin 2 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (branch (normalize P) (constantZero 2) C) (suc r) xs))) :
    Nonempty (Derivation body Γ (programGraph C (suc r) xs)) := by
  let F := programGraph P (suc z) xs
  apply formulaCases F _
  · exact successorBranchElim (normalize P) (constantZero 2) C (suc r) z xs
      (normalizeAccept P xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp h F)
  · have zero := normalizeReject (body := body) (Gamma := F.not :: Γ) P xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have selected := zeroBranchElim (normalize P) (constantZero 2) C (suc r) xs zero (withHyp h F.not)
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc r) z xs selected (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

/-- At either literal named leaf, recover the positive result on the new
output program itself after physically cutting the existing K/lexical layers. -/
theorem exact_OpenNamedResultLanding (b : Bool) (s : Settings) (B : Program 2)
    (ctx ty i result : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph
      (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B))))
      (suc result) ![ctx,namedTerm b.toNat ty i]))) :
    Nonempty (Derivation body Γ (programGraph (namedResultBase B) (suc result) ![ctx,namedTerm b.toNat ty i])) := by
  let raw := namedTerm b.toNat ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let H := namedResultBase B
  let G := onRaw (leafTypeTest s)
  have guarded := exact_OpenNamedGrammarGuardSelected b s (lexicalBoundBase H) ctx ty i result actual
  cases b
  · have noBound := liftReport (header 1 2) ctx raw z (actual_FreeKeyRejectsBoundHeader ty i)
    have namedOnly := requirePositive G (namedGrammarAt true s (lexicalBoundBase H)) result xs guarded
    have lexical := zeroBranchElim (onRaw (header 1 2)) (lexicalBoundBase H)
      (grammarGuard s (lexicalBoundBase H)) (suc result) xs noBound namedOnly
    exact zeroBranchElim (onRaw (header 1 2)) H
      (branch (normalize lexicalGuard) (constantZero 2) H) (suc result) xs noBound lexical
  · have shape := exact_OpenCoverNamedLeafIntrinsicShape true body α Γ ty i
    have lexical := requirePositive G (lexicalBoundBase H) result xs guarded
    have checked := successorBranchElim (onRaw (header 1 2)) H
      (branch (normalize lexicalGuard) (constantZero 2) H) (suc result) z xs
      (liftReport (header 1 2) ctx raw (suc z) shape.2.2.1) lexical
    exact requirePositive lexicalGuard H result xs checked

#print axioms exact_OpenNamedResultLanding

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultLandingProof
