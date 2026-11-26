module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicShapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue valueUnique)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (trans congSuc addZero addSucc sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelope (applyUnary exactBody field)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellGood cellTail)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets

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

private theorem auxReject (ty : OTerm α)
    (head : Nonempty (Derivation body Γ (unary cellHead (numeral 3) (typeLeafTerm ty)))) :
    Nonempty (Derivation body Γ (unary (header 6 4) z (typeLeafTerm ty))) := by
  let raw := typeLeafTerm ty
  let t := literal 1 6
  let E : Program 1 := .composition equalityTest ![cellHead,t]
  let A := applyUnary (exactBody 4) cellTail
  have rejected : Nonempty (Derivation body Γ (unary E z raw)) := by
    apply compositionValue equalityTest ![cellHead,t] z ![raw] ![numeral 3,numeral 6]
      (rejectForwardOrder (numeral 3) (numeral 6) (ltLiteral 3 2))
    intro i
    exact Fin.cases head (Fin.cases (literalGraph 6 ![raw]) (fun j => Fin.elim0 j)) i
  exact rightZero cellGood (conjunction E A) ![raw] (leftZero E A ![raw] rejected)

theorem exact_OpenCoverTypeLeafShape : ExactOpenCoverTypeLeafShape := by
  intro body α Γ ty
  let raw := typeLeafTerm ty
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) (numeral 3) (packedBody [ty])
  have head : Nonempty (Derivation body Γ (unary cellHead (numeral 3) raw)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have tag : Nonempty (Derivation body Γ (unary (literal 1 3) (numeral 3) raw)) := literalGraph 3 ![raw]
  have positive := packedNode (literal 1 3) (numeral 3) [ty] tag
  exact ⟨auxReject ty head,positive.1,positive.2.1⟩

#print axioms exact_OpenCoverTypeLeafShape

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicShapeProof
