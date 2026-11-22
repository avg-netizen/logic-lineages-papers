module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedTargets (parentMeasureAndBounds)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

structure AuxMeasureChild (M : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (q m d b : OTerm α) : Prop where
  observed : Nonempty (Derivation body Γ (measureGraph M chosenCombine m q))
  coords : Nonempty (Derivation body Γ (codePair m d b))

/-- Physical selected measurement and its two genuine ordinary projections,
supplied to a continuation that cannot let the fresh terms escape. -/
def ExactOpenChosenAuxMeasureChildCases : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (q : OTerm α) (goal : Formula α),
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m d b : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      AuxMeasureChild M body Δ (q.relabel j) m d b →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

structure AuxMeasureParentResult (M : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (dom cod fn arg mf ma p df da bf ba : OTerm α) : Prop where
  combined : Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma]))
  parentBounds : Nonempty (Derivation body Γ (parentMeasureAndBounds M dom cod fn arg p df da bf ba))

/-- Physical children and pair reports already present, obtain the actual
chosen combine without supposing its value. The given parent report fixes
that output and all parent bounds at the very same p. -/
def ExactOpenChosenAuxMeasureAlign : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg mf ma p df da bf ba : OTerm α),
    Nonempty (Derivation body Γ (measureGraph M chosenCombine p (auxiliaryTerm dom cod fn arg))) →
    AuxMeasureChild M body Γ fn mf df bf → AuxMeasureChild M body Γ arg ma da ba →
    AuxMeasureParentResult M body Γ dom cod fn arg mf ma p df da bf ba

/-- A single actual chosen parent report at the literal original auxiliary
key suffices. Both actual child codes and their standard pairs, the
binary result at p, and the paired weak bounds are given to the same
continuation. No child observation, pair or binary result is input. -/
def ExactOpenChosenAuxMeasureParent : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg p : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (measureGraph M chosenCombine p (auxiliaryTerm dom cod fn arg))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (mf ma df da bf ba : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      AuxMeasureChild M body Δ (fn.relabel j) mf df bf →
      AuxMeasureChild M body Δ (arg.relabel j) ma da ba →
      AuxMeasureParentResult M body Δ (dom.relabel j) (cod.relabel j)
        (fn.relabel j) (arg.relabel j) mf ma (p.relabel j) df da bf ba →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentTargets
