module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open SourceComputabilityFormulaSupportProof (allOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge seenWitness)
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseScalarEdge (edge4 windowTape)

def windowAt (W : Program 3) {α : Type} (ctx ty k : OTerm α) : Formula α :=
  programGraph W (suc z) (windowTape ctx ty k)

def allWindow (W : Program 3) {α : Type} (ctx ty seen : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((memberGraph (seen.relabel j) k).imp (windowAt W (ctx.relabel j) (ty.relabel j) k))

def TargetWindow (E : Program 4) (W : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty w k : OTerm α),
    Nonempty (Derivation body Γ ((acceptEdge E ctx ty w k).imp (windowAt W ctx ty k)))

/-- The zero edge of the initial round and the actual guarded scalar edge
of successor rounds satisfy the same target-window implication. -/
def ExactRoundEdgeWindows : Prop :=
  ∀ (X : Program 2) (W : Program 3), TargetWindow (constantZero 4) W ∧ TargetWindow (edge4 X W) W

/-- An equal predecessor inherits its earlier membership guard. A genuine
directed edge pays the guard on its target at the same context and type. -/
def ExactSeenWitnessPreservesWindow : Prop :=
  ∀ (E : Program 4) (W : Program 3), TargetWindow E W →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seen k : OTerm α),
      Nonempty (Derivation body Γ ((allWindow W ctx ty seen ⊓ seenWitness E seen ctx ty k).imp
        (windowAt W ctx ty k)))

/-- The full output window is an original universal formula over every
member of that actual pass output. -/
def ExactPassWindowFromRetained : Prop :=
  ExactRetainedPredecessor →
    ∀ (E : Program 4) (W : Program 3), TargetWindow E W →
      ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty vertices seen out : OTerm α),
        Nonempty (Derivation body Γ ((allWindow W ctx ty seen ⊓ passGraph E out vertices seen ctx ty).imp
          (allWindow W ctx ty out)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
