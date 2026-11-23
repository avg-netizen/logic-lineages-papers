module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLexHeaderTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary z)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

def omegaTerm {α : Type} (head base : OTerm α) : OTerm α :=
  rawCons (numeral 4) (rawCons head (rawCons base z))

structure OmegaFields (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (raw head base : OTerm α) : Prop where
  owner : D B Γ (eqn raw (omegaTerm head base))
  headReport : D B Γ (unary (field 0) head raw)
  baseReport : D B Γ (unary (field 1) base raw)

structure FiniteFields (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (raw head outTy label base extras : OTerm α) : Prop where
  owner : D B Γ (eqn raw (numberedTerm head outTy label base extras))
  headReport : D B Γ (unary (field 0) head raw)
  typeReport : D B Γ (unary (field 1) outTy raw)
  labelReport : D B Γ (unary (field 2) label raw)
  baseReport : D B Γ (unary (field 3) base raw)
  extrasReport : D B Γ (unary (field 4) extras raw)

/-- Exact constructor cases, not syntax coverage for an arbitrary raw term.
The ordinary tag has no finite-label or extra-list field. -/
def ExactOpenConstructorLexHeaderCases : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw : OTerm α) (goal : Formula α),
    D B Γ (headerAt 4 2 raw ⊔ headerAt 5 5 raw) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (head base : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      OmegaFields B Δ (raw.relabel j) head base → D B Δ (goal.relabel j)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (head outTy label base extras : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      FiniteFields B Δ (raw.relabel j) head outTy label base extras → D B Δ (goal.relabel j)) →
    D B Γ goal

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLexHeaderTargets
