module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterRetentionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (cell passGraph)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- A successful test of the supplied head gives a genuine occurrence of that
head in the actual output of filtering the enclosing cons. -/
def ExactScannedHeadRetained : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices h tail seen ctx ty out : OTerm α),
    Nonempty (Derivation body Γ
      (((cell vertices h tail ⊓ passGraph E out vertices seen ctx ty) ⊓ scanGraph E seen ctx ty h).imp
        (memberGraph out h)))

/-- The actual output of filtering the same tail can be supplied separately.
Every occurrence in it survives either branch at the head. -/
def ExactFilteredTailRetained : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices h tail seen ctx ty out rest k : OTerm α),
    Nonempty (Derivation body Γ
      (((cell vertices h tail ⊓ passGraph E out vertices seen ctx ty) ⊓
        (passGraph E rest tail seen ctx ty ⊓ memberGraph rest k)).imp (memberGraph out k)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterRetentionTargets
