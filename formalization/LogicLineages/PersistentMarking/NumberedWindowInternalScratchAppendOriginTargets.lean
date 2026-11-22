module

public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph tested appears)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

abbrev backAt {α : Type} (raw suffix k : OTerm α) :=
  (tested raw suffix k).imp (appears raw suffix k)

abbrev backMotive {α : Type} (suffix k : OTerm α) : Formula (α ⊕ Fin 1) :=
  backAt (.var (.inr 0)) (suffix.relabel Sum.inl) (k.relabel Sum.inl)

/-- Recover the side of an actual member of the original append output.
No occurrence index, priority, uniqueness or canonical-input premise. -/
def ExactOpenScratchAppendOrigin : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw suffix out k : OTerm α),
    Nonempty (Derivation body Γ (appendGraph out raw suffix)) →
    Nonempty (Derivation body Γ (memberGraph out k)) →
    Nonempty (Derivation body Γ (appears raw suffix k))

end LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginTargets
