module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildrenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureAt)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior lambdaTape)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaBump)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxTape)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair boundBody)
open NumberedWindowInternalCoverSharedRecursionTargets
open NumberedWindowInternalCoverSharedMemoTargets

structure SelectedMeasureData (R : Program 4) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (q m d b : OTerm α) : Prop where
  selected : Nonempty (Derivation body Γ (unary (selectedMeasure R) m q))
  coordinates : Nonempty (Derivation body Γ (codePair m d b))

def ExactOpenCoverMemoMeasuredChildCases : Prop :=
  ∀ (R : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (q : OTerm α) (goal : Formula α),
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m d b : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      SelectedMeasureData R body Δ (q.relabel j) m d b →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

structure SharedLambdaMeasureRow (M : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ty q old p mc d b : OTerm α) : Prop where
  oldAndStep : ObservedStep (sharedMeasureUpdate M) body Γ (lambdaPrior ty q) old p
  selectedParent : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (lambdaTerm ty q)))
  child : SelectedMeasureData (sharedMeasureUpdate M) body Γ q mc d b
  read : Nonempty (Derivation body Γ (programGraph (measureAt 1) mc (lambdaTape ty q old)))
  combined : Nonempty (Derivation body Γ (unary lambdaBump p mc))
  parentPair : Nonempty (Derivation body Γ (codePair p (suc d) b))

structure SharedAuxMeasureRow (M : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (dom cod fn arg old p mf ma df da bf ba : OTerm α) : Prop where
  oldAndStep : ObservedStep (sharedMeasureUpdate M) body Γ (memoPrior dom cod fn arg) old p
  selectedParent : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (auxiliaryTerm dom cod fn arg)))
  fnData : SelectedMeasureData (sharedMeasureUpdate M) body Γ fn mf df bf
  argData : SelectedMeasureData (sharedMeasureUpdate M) body Γ arg ma da ba
  fnRead : Nonempty (Derivation body Γ (programGraph (measureAt 2) mf (auxTape dom cod fn arg old)))
  argRead : Nonempty (Derivation body Γ (programGraph (measureAt 3) ma (auxTape dom cod fn arg old)))
  combined : Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma]))
  parentBounds : Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba)))

def ExactOpenCoverSharedLambdaMeasureAtRow : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q old p mc d b : OTerm α),
    ObservedStep (sharedMeasureUpdate M) body Γ (lambdaPrior ty q) old p →
    SelectedMeasureData (sharedMeasureUpdate M) body Γ q mc d b →
    SharedLambdaMeasureRow M body Γ ty q old p mc d b

def ExactOpenCoverSharedAuxMeasureAtRow : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg old p mf ma df da bf ba : OTerm α),
    ObservedStep (sharedMeasureUpdate M) body Γ (memoPrior dom cod fn arg) old p →
    SelectedMeasureData (sharedMeasureUpdate M) body Γ fn mf df bf →
    SelectedMeasureData (sharedMeasureUpdate M) body Γ arg ma da ba →
    SharedAuxMeasureRow M body Γ dom cod fn arg old p mf ma df da bf ba

def ExactOpenCoverSharedLambdaMeasureParent : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q p : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (sharedMeasure M) p (lambdaTerm ty q))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old mc d b : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      SharedLambdaMeasureRow M body Δ (ty.relabel j) (q.relabel j) old (p.relabel j) mc d b →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

def ExactOpenCoverSharedAuxMeasureParent : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg p : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (sharedMeasure M) p (auxiliaryTerm dom cod fn arg))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old mf ma df da bf ba : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      SharedAuxMeasureRow M body Δ (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
        old (p.relabel j) mf ma df da bf ba →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildrenTargets
