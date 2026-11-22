module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverAscendingRangeTargets (rangeTest rangeReport)

/-- Every actual member of the exact physical ascending range output
satisfies the original strict bound in the object calculus. -/
def ExactOpenCoverAscendingRangeOrigin : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out bound i : OTerm α),
    Nonempty (Derivation body Γ (rangeReport out bound)) →
    Nonempty (Derivation body Γ (memberGraph out i)) →
    Nonempty (Derivation body Γ (ltF i bound))

abbrev backBound {α : Type} (bound i : OTerm α) : Formula α :=
  (rangeTest bound i).imp (ltF i bound)

abbrev backMotive {α : Type} (i : OTerm α) : Formula (α ⊕ Fin 1) :=
  backBound (.var (.inr 0)) (i.relabel Sum.inl)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginTargets
