module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalPairingOrderArithmeticProof (addStrictRight)
open ID1Completion.InternalUnpairArithmeticProof (addStrictLeft leftWeakAdd)
open ID1Completion.InternalUnpairReverseBoundsArithmeticProof (rightWeakAdd weakTrans squareSelfWeak)
open ID1Completion.InternalPairingSumBoundsArithmeticProof (addWeakLeft)
open ID1Completion.InternalSquareRootArithmetic (square)
open ID1Completion.InternalSquareRootArithmeticSupportProof
  (strictTrans strictWeakTrans rightSuccessor squareStrictMonotonicity)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxExchangeKeyTargets

theorem exact_OpenRawConsBounds : ExactOpenRawConsBounds := by
  intro body α Γ head tail
  let sum := add head tail
  have sumWeak := squareSelfWeak (body := body) (Gamma := Γ) sum
  have squareWeak := leftWeakAdd (body := body) (Gamma := Γ) (square sum) head
  exact ⟨weakTrans head (square sum) (pairTerm head tail)
      (weakTrans head sum (square sum) (leftWeakAdd head tail) sumWeak) squareWeak,
    weakTrans tail (square sum) (pairTerm head tail)
      (weakTrans tail sum (square sum) (rightWeakAdd head tail) sumWeak) squareWeak⟩

theorem exact_OpenSparsePairStrict : ExactOpenSparsePairStrict := by
  intro body α Γ x y a b left right
  let low := add x y
  let high := add a b
  have sums : Nonempty (Derivation body Γ (ltF low high)) :=
    strictTrans low (add a y) high (addStrictRight x a y left) (addStrictLeft a y b right)
  have squares := squareStrictMonotonicity low high sums
  have before := addStrictRight (square low) (square high) x squares
  have after := addWeakLeft (square high) x a (rightSuccessor x a left)
  exact strictWeakTrans (pairTerm x y) (add (square high) x) (pairTerm a b) before after

private theorem functionBelow {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (dom cod fn arg : OTerm α) : Nonempty (Derivation body Γ (ltF fn (auxiliaryTerm dom cod fn arg))) := by
  let last := rawCons arg z
  let head := rawCons fn last
  let codomain := rawCons cod head
  let domain := rawCons dom codomain
  let parent := rawCons (numeral 6) domain
  exact strictTrans fn domain parent
    (strictTrans fn codomain domain
      (strictTrans fn head codomain (exact_OpenRawConsBounds body α Γ fn last).1
        (exact_OpenRawConsBounds body α Γ cod head).2)
      (exact_OpenRawConsBounds body α Γ dom codomain).2)
    (exact_OpenRawConsBounds body α Γ (numeral 6) domain).2

theorem exact_OpenAuxFunctionKeyDecrease : ExactOpenAuxFunctionKeyDecrease := by
  intro body α Γ dom cod fn fn' arg
  exact exact_OpenSparsePairStrict body α Γ fn fn' (auxiliaryTerm dom cod fn arg)
    (auxiliaryTerm dom cod fn' arg) (functionBelow dom cod fn arg) (functionBelow dom cod fn' arg)

#print axioms exact_OpenRawConsBounds
#print axioms exact_OpenSparsePairStrict
#print axioms exact_OpenAuxFunctionKeyDecrease

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyChecks
