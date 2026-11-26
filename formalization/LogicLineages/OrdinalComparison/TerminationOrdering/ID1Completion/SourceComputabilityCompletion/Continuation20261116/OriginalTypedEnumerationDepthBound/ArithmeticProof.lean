module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.OrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (trans congSuc refl)
open InternalAdditionLawsProof (add leftSuccessor)
open InternalOriginalPairingOrderArithmeticProof
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open InternalSquareRootArithmeticSupportProof (rightSuccessor)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def doubleSuccessor (size : OTerm alpha) :
    Derivation body Delta (eqn (twice (suc size)) (suc (suc (twice size)))) :=
  trans (leftSuccessor size (suc size)) (congSuc (InternalTagArithmeticSupportProof.addSucc size size))

theorem doubleSuccessorChecked (size : OTerm alpha) :
    Nonempty (Derivation body Delta (eqn (twice (suc size)) (suc (suc (twice size))))) :=
  ⟨doubleSuccessor size⟩

theorem doubleMonotone (s t : OTerm alpha)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess s (suc t)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess (twice s) (suc (twice t)))) :=
  addWeakBoth s t s t h h

theorem termMonotone (d s t : OTerm alpha)
    (h : Nonempty (Derivation body Delta (termBound d s)))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess s (suc t)))) :
    Nonempty (Derivation body Delta (termBound d t)) :=
  weakTrans d (twice s) (twice t) h (doubleMonotone s t hs)

theorem argumentsMonotone (d s t : OTerm alpha)
    (h : Nonempty (Derivation body Delta (argumentsBound d s)))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess s (suc t)))) :
    Nonempty (Derivation body Delta (argumentsBound d t)) :=
  weakTrans d (suc (twice s)) (suc (twice t)) h
    (OriginalEnumerationMembership.OrderProof.successorForward (twice s) (suc (twice t)) (doubleMonotone s t hs))

theorem termToArguments (d s : OTerm alpha)
    (h : Nonempty (Derivation body Delta (termBound d s))) :
    Nonempty (Derivation body Delta (argumentsBound d s)) :=
  rightSuccessor d (suc (twice s)) h

theorem unaryGrowth (d s : OTerm alpha)
    (h : Nonempty (Derivation body Delta (argumentsBound d s))) :
    Nonempty (Derivation body Delta (termBound (suc d) (suc s))) := by
  have hd := OriginalEnumerationMembership.OrderProof.successorForward d (suc (suc (twice s))) h
  exact strictTransport (suc d) (suc (twice (suc s))) (suc d) (suc (suc (suc (twice s))))
    ⟨refl _⟩ ⟨congSuc (doubleSuccessor s)⟩ hd

theorem positiveSuccessor (s : OTerm alpha) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess z (suc s))) :=
  ⟨InternalQuotientComparisonProof.zeroLessSuccessor s⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArithmeticProof
