module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalBase)

/-- Directed physical report transport at *one* fixed object tape,
stable under allowed reindexing and contextual enlargement. It is not
pointwise numerical evaluation, equivalence, or unrestricted graph transfer. -/
def TapeForward {n : Nat} (P Q : Program n) (body : Positive (Fin 1)) {α : Type}
    (Γ : List (Formula α)) (xs : Fin n → OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    Nonempty (Derivation body Δ (programGraph P out (fun i => (xs i).relabel j))) →
    Nonempty (Derivation body Δ (programGraph Q out (fun i => (xs i).relabel j)))

def ExactOpenCoverBranchTapeForward : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (α : Type) (Γ : List (Formula α))
    (xs : Fin n → OTerm α) (C C' P P' Q Q' : Program n),
    TapeForward C C' body Γ xs →
    TapeForward P P' body Γ xs →
    TapeForward Q Q' body Γ xs →
    TapeForward (branch C P Q) (branch C' P' Q') body Γ xs

def ExactOpenCoverLambdaBaseTapeForward : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx raw : OTerm α),
    Nonempty (Derivation body Γ (unary (header 2 2) z raw)) →
    TapeForward B (lambdaLexicalBase s B T) body Γ ![ctx,raw]

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardTargets
