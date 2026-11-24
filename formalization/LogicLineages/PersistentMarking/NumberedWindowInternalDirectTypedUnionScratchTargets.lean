module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)

abbrev observer {α : Type} (count : Program 2) (lhs rhs : OTerm α) : Formula α :=
  programGraph count (suc z) ![lhs,rhs]

/-- A separate, strictly pointwise object law about the supplied observer.
No typedness, union, or equality of list codes is assumed. Only the
direction the actual union carrier uses is requested. -/
def CountMembershipForward (B : Positive (Fin 1)) (count : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (lhs rhs key : OTerm α),
    Nonempty (Derivation B Γ (observer count lhs rhs)) →
    Nonempty (Derivation B Γ (memberGraph lhs key)) →
    Nonempty (Derivation B Γ (memberGraph rhs key))

def ExactTypedUnionScratch : Prop :=
  ∀ (i : Program 1) (count : Program 2) (B : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (left right lhs joined : OTerm α),
    CountMembershipForward B count →
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) left)) →
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) right)) →
    Nonempty (Derivation B Γ (appendGraph joined left right)) →
    Nonempty (Derivation B Γ (observer count lhs joined)) →
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) lhs))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchTargets
