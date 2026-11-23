module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchIntroTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (allOne)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)

def allMembers {α : Type} (i : Program 1) (code : OTerm α) : Formula α :=
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((memberGraph (code.relabel Sum.inl) k).imp (unary i (suc z) k))

def fromAllMembers {α : Type} (i : Program 1) (code : OTerm α) : Formula α :=
  (allMembers i code).imp (unary (typedScratch i) (suc z) code)

abbrev invariant {α : Type} (i : Program 1) : Formula (α ⊕ Fin 1) :=
  fromAllMembers i (.var (.inr 0))

def ExactTypedScratchAllMembers : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code : OTerm α),
    Nonempty (Derivation B Γ ((unary (typedScratch i) (suc z) code).iff (allMembers i code)))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersTargets
