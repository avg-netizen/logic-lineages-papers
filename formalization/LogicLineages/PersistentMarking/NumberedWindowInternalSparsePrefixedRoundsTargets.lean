module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersClosureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity (included)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

/-- The literal directed filter on the supplied upper list and the original
vertices returns a list whose members are already in upper. -/
def prefixed {α : Type} (E : Program 4) (vertices ctx ty upper later : OTerm α) : Formula α :=
  passGraph E later vertices upper ctx ty ⊓ included later upper

def ExactInitialInUpper : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed upper out : OTerm α),
    Nonempty (Derivation body Γ ((roundGraph E out z vertices ctx ty seed ⊓ memberGraph upper seed).imp
      (included out upper)))

def ExactStepInUpper : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed upper later i before after : OTerm α),
    let runs := roundGraph E before i vertices ctx ty seed ⊓ roundGraph E after (suc i) vertices ctx ty seed
    Nonempty (Derivation body Γ ((prefixed E vertices ctx ty upper later ⊓ (runs ⊓ included before upper)).imp
      (included after upper)))

/-- Every genuine round lies inside any such upper list containing the seed. -/
def ExactRoundsInUpper : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed upper later i out : OTerm α),
    Nonempty (Derivation body Γ (((memberGraph upper seed ⊓ prefixed E vertices ctx ty upper later) ⊓
      roundGraph E out i vertices ctx ty seed).imp (included out upper)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsTargets
