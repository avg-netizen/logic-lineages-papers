module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxPairDecreaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalSquareRootArithmeticSupportProof (strictTrans)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxExchangeKeyChecks
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenAuxiliaryFunctionBelow (d c f a : OTerm α) :
    Nonempty (Derivation B Γ (ltF f (auxiliaryTerm d c f a))) := by
  let last := rawCons a z
  let fn := rawCons f last
  let cod := rawCons c fn
  let dom := rawCons d cod
  let root := rawCons (numeral 6) dom
  exact strictTrans f dom root
    (strictTrans f cod dom
      (strictTrans f fn cod (exact_OpenRawConsBounds B α Γ f last).1
        (exact_OpenRawConsBounds B α Γ c fn).2)
      (exact_OpenRawConsBounds B α Γ d cod).2)
    (exact_OpenRawConsBounds B α Γ (numeral 6) dom).2

theorem exact_OpenAuxiliaryArgumentBelow (d c f a : OTerm α) :
    Nonempty (Derivation B Γ (ltF a (auxiliaryTerm d c f a))) := by
  let last := rawCons a z
  let fn := rawCons f last
  let cod := rawCons c fn
  let dom := rawCons d cod
  let root := rawCons (numeral 6) dom
  exact strictTrans a dom root
    (strictTrans a cod dom
      (strictTrans a fn cod
        (strictTrans a last fn (exact_OpenRawConsBounds B α Γ a z).1
          (exact_OpenRawConsBounds B α Γ f last).2)
        (exact_OpenRawConsBounds B α Γ c fn).2)
      (exact_OpenRawConsBounds B α Γ d cod).2)
    (exact_OpenRawConsBounds B α Γ (numeral 6) dom).2

/-- Both possible nested calls are on the actual earlier sparse pair
key, independent of which of the two coordinates was unchanged. -/
theorem exact_OpenTypedAuxiliaryPairDecrease (a b : AuxRow α) :
    Nonempty (Derivation B Γ (ltF (pairTerm a.fn b.fn) (pairTerm a.term b.term))) ∧
    Nonempty (Derivation B Γ (ltF (pairTerm a.arg b.arg) (pairTerm a.term b.term))) := by
  exact ⟨exact_OpenSparsePairStrict B α Γ a.fn b.fn a.term b.term
    (exact_OpenAuxiliaryFunctionBelow a.dom a.cod a.fn a.arg)
    (exact_OpenAuxiliaryFunctionBelow b.dom b.cod b.fn b.arg),
    exact_OpenSparsePairStrict B α Γ a.arg b.arg a.term b.term
    (exact_OpenAuxiliaryArgumentBelow a.dom a.cod a.fn a.arg)
    (exact_OpenAuxiliaryArgumentBelow b.dom b.cod b.fn b.arg)⟩

#print axioms exact_OpenAuxiliaryFunctionBelow
#print axioms exact_OpenAuxiliaryArgumentBelow
#print axioms exact_OpenTypedAuxiliaryPairDecrease
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxPairDecreaseProof
