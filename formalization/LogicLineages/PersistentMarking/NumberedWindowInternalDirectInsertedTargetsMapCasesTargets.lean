module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapCasesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets scratchTargets)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)

/-- Successful output of the physical raw map opens the actual parser and
the ordered scratch projection at precisely that same positive output. -/
def ExactOpenRawMapCases : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (raw result : OrdinaryArithmetic.Term α) (goal : Formula α),
    Nonempty (Derivation B Γ (unary insertedTargets (suc result) raw)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (decoded : OrdinaryArithmetic.Term β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (unary parser (suc decoded) (raw.relabel j))) →
      Nonempty (Derivation B Δ (unary scratchTargets (suc (result.relabel j)) decoded)) →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapCasesTargets
