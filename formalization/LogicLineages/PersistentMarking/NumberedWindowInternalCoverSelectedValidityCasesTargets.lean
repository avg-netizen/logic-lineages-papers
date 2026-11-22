module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityCasesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports packedBody)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt layout selectedValidity)

/-- An object-language conclusion consumes one of the original physical
branches; fresh fields stay inside its graph cuts. Membership of
(tag,arity) in the fixed ordered layout is the external branch index. -/
def ValidBranchCase (xs : List (Nat × Nat)) (V : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (q : OTerm α) (goal : Formula α) : Prop :=
  ∀ (tag arity : Nat), (tag,arity) ∈ xs →
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (fields : List (OTerm β)),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    fields.length = arity →
    Reports body Δ (q.relabel j) cellTail fields →
    Nonempty (Derivation body Δ (eqn (q.relabel j) (rawCons (numeral tag) (packedBody fields)))) →
    Nonempty (Derivation body Δ (headerAt tag arity (q.relabel j))) →
    Nonempty (Derivation body Δ (unary V (suc z) (q.relabel j))) →
    Nonempty (Derivation body Δ (unary (selectedValidity V) (suc z) (q.relabel j))) →
    Nonempty (Derivation body Δ (goal.relabel j))

/-- Exact seven-case eliminator from actual V-prime success, not from
calibration of an unchanged validity callback. -/
def ExactOpenCoverSelectedValidityCases : Prop :=
  ∀ (V : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (q : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (selectedValidity V) (suc z) q)) →
    ValidBranchCase layout V body Γ q goal →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityCasesTargets
