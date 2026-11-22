module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports packedBody)
open NumberedWindowInternalCoverSelectedValidityTargets (header headerAt)

def ExactCoverHeaderUnpackNode : Prop :=
  ∀ (tag arity raw : Nat), run (header tag arity) raw = 1 ↔
    ∃ fields, unpackNode raw = some (tag,fields) ∧ fields.length = arity

/-- The same actual header, its original ordered field selectors, and
the canonical sparse packing equation for this very same raw key.
An arbitrary object conclusion may consume those actual witnesses but
may not let their fresh variables escape. -/
def ExactOpenCoverHeaderFields : Prop :=
  ∀ (tag arity : Nat) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (q : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (headerAt tag arity q)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (fields : List (OTerm β)),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      fields.length = arity →
      Reports body Δ (q.relabel j) cellTail fields →
      Nonempty (Derivation body Δ
        (eqn (q.relabel j) (rawCons (numeral tag) (packedBody fields)))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets
