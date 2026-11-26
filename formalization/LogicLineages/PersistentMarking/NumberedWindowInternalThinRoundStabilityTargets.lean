module
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundStabilityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalScratchInclusionThinProof (included)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)

/-- Each accepting scan on the first list still accepts on any internally
larger seen list; the directed edge and all its other arguments stay fixed. -/
def ExactScanMonotonicity : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (left right ctx ty k : OTerm α),
    Nonempty (Derivation body Γ ((included left right ⊓ scanGraph E left ctx ty k).imp
      (scanGraph E right ctx ty k)))

/-- Filter exactly the same vertices against two included seen lists. -/
def ExactPassMonotonicity : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices left right ctx ty a b : OTerm α),
    let runs := passGraph E a vertices left ctx ty ⊓ passGraph E b vertices right ctx ty
    Nonempty (Derivation body Γ ((included left right ⊓ runs).imp (included a b)))

/-- Once no new member entered, no new member enters in the following
round either. The three given output graphs are actual successive rounds. -/
def ExactStableNext : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed fuel a b c : OTerm α),
    let runs := roundGraph E a fuel vertices ctx ty seed ⊓
      (roundGraph E b (suc fuel) vertices ctx ty seed ⊓ roundGraph E c (suc (suc fuel)) vertices ctx ty seed)
    Nonempty (Derivation body Γ ((runs ⊓ included b a).imp (included c b)))

end LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundStabilityTargets
