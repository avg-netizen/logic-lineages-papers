module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior lambdaTape)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverLambdaMeasureRowTargets

structure LambdaMeasureEvidence (M : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ty q old mc p d w : OTerm α) : Prop where
  table : Nonempty (Derivation body Γ (tableAt (lambdaMeasureUpdate M) old (lambdaPrior ty q)))
  update : Nonempty (Derivation body Γ (programGraph (lambdaMeasureUpdate M) p (lambdaTape ty q old)))
  child : Nonempty (Derivation body Γ (unary (lambdaMeasure M) mc q))
  childPair : Nonempty (Derivation body Γ (codePair mc d w))
  recovered : Nonempty (Derivation body Γ (lambdaMeasureRecovered M ty q old mc p d w))

def MeasuredCoordinatesCase (M : Program 1) (body : Positive (Fin 1)) {α : Type}
    (Γ : List (Formula α)) (ty q mc p d w : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    LambdaMeasureEvidence M body Δ (ty.relabel j) (q.relabel j) old
      (mc.relabel j) (p.relabel j) (d.relabel j) (w.relabel j) →
    Nonempty (Derivation body Δ (goal.relabel j))

def ExactOpenCoverLambdaSelectedMeasureAtCoordinates : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q mc p d w : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (lambdaMeasure M) p (lambdaTerm ty q))) →
    Nonempty (Derivation body Γ (unary (lambdaMeasure M) mc q)) →
    Nonempty (Derivation body Γ (codePair mc d w)) →
    MeasuredCoordinatesCase M body Γ ty q mc p d w goal →
    Nonempty (Derivation body Γ goal)

/-- The child measurement, ordinary coordinates and earlier table are
genuine witnesses obtained internally, not additional input reports. -/
def ExactOpenCoverLambdaSelectedMeasure : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q p : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (lambdaMeasure M) p (lambdaTerm ty q))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old mc d w : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      LambdaMeasureEvidence M body Δ (ty.relabel j) (q.relabel j) old mc (p.relabel j) d w →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

def ExactOpenCoverLambdaSelectedMeasureAtHeader : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw p : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (lambdaMeasure M) p raw)) →
    Nonempty (Derivation body Γ (headerAt 2 2 raw)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ty q old mc d w : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Reports body Δ (raw.relabel j) cellTail [ty,q] →
      Nonempty (Derivation body Δ (eqn (raw.relabel j) (lambdaTerm ty q))) →
      LambdaMeasureEvidence M body Δ ty q old mc (p.relabel j) d w →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureTargets
