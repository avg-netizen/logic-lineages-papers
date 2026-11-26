module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)

def fromMember {α : Type} (i : Program 1) (code key : OTerm α) : Formula α :=
  (unary (typedScratch i) (suc z) code ⊓ memberGraph code key).imp (unary i (suc z) key)

abbrev invariant {α : Type} (i : Program 1) (key : OTerm α) : Formula (α ⊕ Fin 1) :=
  fromMember i (.var (.inr 0)) (key.relabel Sum.inl)

/-- At any actual open member, same scalar call returns literal unit. -/
def ExactTypedScratchMember : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code key : OTerm α),
    Nonempty (Derivation B Γ (fromMember i code key))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberTargets
