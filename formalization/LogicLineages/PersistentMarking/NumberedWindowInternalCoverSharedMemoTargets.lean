module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (childAt measureAt)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSharedRecursionTargets

structure ObservedStep (R : Program 4) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (prior old out : OTerm α) : Prop where
  table : Nonempty (Derivation body Γ (tableAt R old prior))
  update : Nonempty (Derivation body Γ (programGraph R out ![prior,old,z,z]))

/-- Observe the actual prior table and actual step for the given output of
one fixed selected unary memo. The row has the same updater and output. -/
def ExactOpenCoverSharedMemoRowCases : Prop :=
  ∀ (R : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (prior out : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (selectedMeasure R) out (suc prior))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      ObservedStep R body Δ (prior.relabel j) old (out.relabel j) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

/-- An actual lookup on that same earlier physical table determines the
selected report of the genuinely smaller, literally selected child.
The result is arbitrary, so this applies to both V⋆ and M⋆. -/
def ExactOpenCoverSharedMemoEarlierValue : Prop :=
  ∀ (R : Program 4) (slot : Nat) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (child prior old out : OTerm α),
    Nonempty (Derivation body Γ (programGraph currentKey (suc prior) ![prior,old,z,z])) →
    Nonempty (Derivation body Γ (programGraph (childAt slot) child ![prior,old,z,z])) →
    Nonempty (Derivation body Γ (ltF child (suc prior))) →
    Nonempty (Derivation body Γ (tableAt R old prior)) →
    Nonempty (Derivation body Γ (programGraph (measureAt slot) out ![prior,old,z,z])) →
    Nonempty (Derivation body Γ (unary (selectedMeasure R) out child))

def sharedLambdaChildren {α : Type} (V T : Program 1) (ty q : OTerm α) : Formula α :=
  unary T (suc z) ty ⊓ unary (sharedSyntax V T) (suc z) q

def sharedAuxChildren {α : Type} (V T : Program 1) (dom cod fn arg : OTerm α) : Formula α :=
  (unary T (suc z) dom ⊓ unary T (suc z) cod) ⊓
    (unary (sharedSyntax V T) (suc z) fn ⊓ unary (sharedSyntax V T) (suc z) arg)

def ExactOpenCoverSharedLambdaSyntaxParent : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q : OTerm α),
    Nonempty (Derivation body Γ (unary (sharedSyntax V T) (suc z) (lambdaTerm ty q))) →
    Nonempty (Derivation body Γ (sharedLambdaChildren V T ty q))

def ExactOpenCoverSharedAuxSyntaxParent : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg : OTerm α),
    Nonempty (Derivation body Γ (unary (sharedSyntax V T) (suc z) (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (sharedAuxChildren V T dom cod fn arg))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets
