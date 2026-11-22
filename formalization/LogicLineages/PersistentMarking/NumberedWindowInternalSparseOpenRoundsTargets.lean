module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)
open NumberedWindowInternalSparseDirectedFilter (cell passGraph)
open NumberedWindowInternalSparseDirectedRounds

def roundGraph {α : Type} (E : Program 4) (out fuel vertices ctx ty seed : OTerm α) : Formula α :=
  programGraph (rounds E) out (roundsTape fuel vertices ctx ty seed)

/-- Round zero filters the original vertices against the physical singleton seed. -/
def ExactOpenRoundZero : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out vertices ctx ty seed singleton : OTerm α),
    Nonempty (Derivation body Γ ((cell singleton seed z).imp
      (equivalent (roundGraph E out z vertices ctx ty seed)
        (passGraph (constantZero 4) out vertices singleton ctx ty))))

/-- Every successor uses both the same vertices and the actual previous output,
including all occurrences, under the original directed edge. -/
def ExactOpenRoundSuccessor : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out fuel vertices ctx ty seed previous : OTerm α),
    Nonempty (Derivation body Γ ((roundGraph E previous fuel vertices ctx ty seed).imp
      (equivalent (roundGraph E out (suc fuel) vertices ctx ty seed)
        (passGraph E out vertices previous ctx ty))))

/-- The chosen fuel is the literal scratch length evaluated on the same supplied vertices. -/
def ExactOpenMembersAtLength : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out fuel vertices ctx ty seed : OTerm α),
    Nonempty (Derivation body Γ ((unary poolLength fuel vertices).imp
      (equivalent (programGraph (members E) out (membersTape vertices ctx ty seed))
        (roundGraph E out fuel vertices ctx ty seed))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
