module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

/-- The two literal sparse fields are each strictly below their cons code. -/
def ExactOpenRawConsBounds : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (head tail : OTerm α),
    Nonempty (Derivation body Γ (ltF head (rawCons head tail))) ∧
    Nonempty (Derivation body Γ (ltF tail (rawCons head tail)))

/-- Strict comparison of the real sparse pair polynomial in both coordinates. -/
def ExactOpenSparsePairStrict : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (x y a b : OTerm α),
    Nonempty (Derivation body Γ (ltF x a)) → Nonempty (Derivation body Γ (ltF y b)) →
    Nonempty (Derivation body Γ (ltF (pairTerm x y) (pairTerm a b)))

/-- The precise table key needed by the function-side tag-six exchange branch. -/
def ExactOpenAuxFunctionKeyDecrease : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (dom cod fn fn' arg : OTerm α),
    Nonempty (Derivation body Γ (ltF (pairTerm fn fn')
      (pairTerm (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg))))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyTargets
