module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseScalarEdge (edge4)

def observed (M : Program 5) {α : Type} (ctx dom cod arg k value : OTerm α) : Formula α :=
  programGraph M value ![k,ctx,dom,cod,arg]

def edgeRow (E : Program 4) (M : Program 5) {α : Type} (ctx ty dom cod arg value : OTerm α) : Formula (α ⊕ Fin 2) :=
  let j : α → α ⊕ Fin 2 := Sum.inl
  let f : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let g : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  (acceptEdge E (ctx.relabel j) (ty.relabel j) f g ⊓
    observed M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) f (value.relabel j)).imp
    (observed M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) g (value.relabel j))

/-- Preservation for the fixed open observation, in the same original object context. -/
def closed (E : Program 4) (M : Program 5) {α : Type} (ctx ty dom cod arg value : OTerm α) : Formula α :=
  allBlock (edgeRow E M ctx ty dom cod arg value)

def source (E : Program 4) (M : Program 5) {α : Type} (ctx ty dom cod arg seed value : OTerm α) : Formula α :=
  closed E M ctx ty dom cod arg value ⊓ observed M ctx dom cod arg seed value

def inputs (E : Program 4) (M : Program 5) {α : Type}
    (i vertices ctx ty seed out k value dom cod arg : OTerm α) : Formula α :=
  source E M ctx ty dom cod arg seed value ⊓ (roundGraph E out i vertices ctx ty seed ⊓ memberGraph out k)

/-- Transmit the same physical program output through each actual directed round. -/
def ExactRoundObservation : Prop :=
  ∀ (E : Program 4) (M : Program 5) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (i vertices ctx ty seed out k value dom cod arg : OTerm α),
    Nonempty (Derivation body Γ ((inputs E M i vertices ctx ty seed out k value dom cod arg).imp
      (observed M ctx dom cod arg k value)))

/-- The same transport to the selected representative uses the actual successful packed least. -/
def ExactSelectedObservation : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (M : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty dom cod arg seed selected value : OTerm α),
    Nonempty (Derivation body Γ ((source (edge4 X W) M ctx ty dom cod arg seed value ⊓
      leastGraph C X W s ctx ty seed selected).imp (observed M ctx dom cod arg selected value)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationTargets
