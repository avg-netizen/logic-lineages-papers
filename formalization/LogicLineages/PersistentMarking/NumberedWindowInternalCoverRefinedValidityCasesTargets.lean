module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedValidityCasesTargets
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
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt headersAt layout)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedSyntax)

/-- An object-language conclusion consumes one of the original physical
branches; fresh fields stay inside its graph cuts. Membership of
(tag,arity) in the fixed ordered layout is the external branch index. -/
def OriginalBranchCase (xs : List (Nat × Nat)) (V : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (q : OTerm α) (goal : Formula α) : Prop :=
  ∀ (tag arity : Nat), (tag,arity) ∈ xs →
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (fields : List (OTerm β)),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    fields.length = arity →
    Reports body Δ (q.relabel j) cellTail fields →
    Nonempty (Derivation body Δ (eqn (q.relabel j) (rawCons (numeral tag) (packedBody fields)))) →
    Nonempty (Derivation body Δ (headerAt tag arity (q.relabel j))) →
    Nonempty (Derivation body Δ (unary V (suc z) (q.relabel j))) →
    Nonempty (Derivation body Δ (goal.relabel j))

/-- Reuse a genuine physical header disjunction regardless of the chosen
validity callback, carrying exactly that same positive unary report. -/
def ExactOpenCoverOriginalHeaderCases : Prop :=
  ∀ (V : Program 1) (xs : List (Nat × Nat)) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (q : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary V (suc z) q)) →
    Nonempty (Derivation body Γ (headersAt xs q)) →
    OriginalBranchCase xs V body Γ q goal →
    Nonempty (Derivation body Γ goal)

/-- All seven original physical branches from the actual refined
shared memo; no old-program validity is asserted. -/
def ExactOpenCoverRefinedValidityCases : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (q : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (refinedSyntax V T) (suc z) q)) →
    OriginalBranchCase layout (refinedSyntax V T) body Γ q goal →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedValidityCasesTargets
