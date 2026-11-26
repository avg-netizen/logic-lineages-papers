module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxMeasureStepTargets (earlierAt)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets

/-- One physical predecessor table, the accepted update on that same tape,
the genuine earlier guard and the recovered annotation/child/lookup. -/
structure LambdaRowEvidence (V T : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ty q old : OTerm α) : Prop where
  table : Nonempty (Derivation body Γ (tableAt (lambdaSyntaxUpdate V T) old (lambdaPrior ty q)))
  update : Nonempty (Derivation body Γ (programGraph (lambdaSyntaxUpdate V T) (suc z) (lambdaTape ty q old)))
  earlier : Nonempty (Derivation body Γ (programGraph (earlierAt 1) (suc z) (lambdaTape ty q old)))
  recovered : Nonempty (Derivation body Γ (lambdaRecovered V T ty q old))

def LiteralLambdaRowCase (V T : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ty q : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    LambdaRowEvidence V T body Δ (ty.relabel j) (q.relabel j) old →
    Nonempty (Derivation body Δ (goal.relabel j))

def ExactOpenCoverLambdaSelectedRow : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (lambdaSyntax V T) (suc z) (lambdaTerm ty q))) →
    LiteralLambdaRowCase V T body Γ ty q goal →
    Nonempty (Derivation body Γ goal)

/-- Optional nonliteral entry: an actual header determines ordered fields
of this same parent and then the physical selected lambda row. -/
def ExactOpenCoverLambdaSelectedRowAtHeader : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (lambdaSyntax V T) (suc z) raw)) →
    Nonempty (Derivation body Γ (headerAt 2 2 raw)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ty q old : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Reports body Δ (raw.relabel j) cellTail [ty,q] →
      Nonempty (Derivation body Δ (eqn (raw.relabel j) (lambdaTerm ty q))) →
      LambdaRowEvidence V T body Δ ty q old →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowTargets
