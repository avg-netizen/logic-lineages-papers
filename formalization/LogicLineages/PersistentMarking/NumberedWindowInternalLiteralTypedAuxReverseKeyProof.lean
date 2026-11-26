module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxPairDecreaseProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxReverseKeyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalSquareRootArithmetic (square)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalAdditionCancellationProof (commutativity)
open ID1Completion.InternalSquareRootArithmeticSupportProof
  (strictTrans strictWeakTrans nextSquareWeak orderLeft)
open ID1Completion.InternalPairingSumBoundsArithmeticProof (successorWeak)
open ID1Completion.InternalOriginalPairingOrderArithmeticProof (addStrictRight)
open ID1Completion.InternalUnpairArithmeticProof (addStrictLeft leftWeakAdd offsetInterval)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxPairDecreaseProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
local notation "D" => Nonempty ∘ Derivation B Γ

/-- The sum separates the entire square intervals, not just the
coordinatewise ordered pair. The result therefore pays either orientation
of a smaller memo row without comparing the parent pair coordinates. -/
theorem exact_OpenSparsePairSumStrict (x y a b : OTerm α) (sum : D (ltF (add x y) (add a b))) :
    D (ltF (pairTerm x y) (pairTerm a b)) := by
  let lo := add x y
  let hi := add a b
  have small : D (ltF x (suc (add lo lo))) :=
    strictWeakTrans x (suc lo) (suc (add lo lo)) (leftWeakAdd x y)
      (successorWeak lo (add lo lo) (leftWeakAdd lo lo))
  obtain ⟨window⟩ := offsetInterval lo x small
  exact strictWeakTrans (pairTerm x y) (square hi) (pairTerm a b)
    (strictWeakTrans (pairTerm x y) (square (suc lo)) (square hi)
      ⟨Derivation.conjunctionRight window⟩ (nextSquareWeak lo hi sum))
    (leftWeakAdd (square hi) a)

theorem exact_OpenSparsePairReverseChildStrict (x y a b : OTerm α)
    (left : D (ltF x a)) (right : D (ltF y b)) : D (ltF (pairTerm y x) (pairTerm a b)) := by
  obtain ⟨sum⟩ := strictTrans (add x y) (add a y) (add a b)
    (addStrictRight x a y left) (addStrictLeft a y b right)
  exact exact_OpenSparsePairSumStrict y x a b ⟨orderLeft (add a b) (commutativity x y) sum⟩

theorem exact_OpenAuxiliaryReverseChildKeys (a b : AuxRow α) :
    D (ltF (pairTerm b.fn a.fn) (pairTerm a.term b.term)) ∧
    D (ltF (pairTerm b.arg a.arg) (pairTerm a.term b.term)) :=
  ⟨exact_OpenSparsePairReverseChildStrict a.fn b.fn a.term b.term
    (exact_OpenAuxiliaryFunctionBelow a.dom a.cod a.fn a.arg)
    (exact_OpenAuxiliaryFunctionBelow b.dom b.cod b.fn b.arg),
    exact_OpenSparsePairReverseChildStrict a.arg b.arg a.term b.term
    (exact_OpenAuxiliaryArgumentBelow a.dom a.cod a.fn a.arg)
    (exact_OpenAuxiliaryArgumentBelow b.dom b.cod b.fn b.arg)⟩

#print axioms exact_OpenSparsePairSumStrict
#print axioms exact_OpenSparsePairReverseChildStrict
#print axioms exact_OpenAuxiliaryReverseChildKeys
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxReverseKeyProof
