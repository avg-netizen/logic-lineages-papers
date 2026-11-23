module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept rowAccept)

def fromMember {α : Type} (r : Program 3) (code removed k : OrdinaryArithmetic.Term α) : Formula α :=
  (loopAccept r code removed ⊓ memberGraph code k).imp (rowAccept r k removed)

abbrev invariant {α : Type} (r : Program 3) (removed k : OrdinaryArithmetic.Term α) :
    Formula (α ⊕ Fin 1) :=
  fromMember r (.var (.inr 0)) (removed.relabel Sum.inl) (k.relabel Sum.inl)

/-- Every actual scratch member of the existing accepting loop is checked
by the same original inserted-row callback. This is internal object-list
induction, not external enumeration or an occurrence-count statement. -/
def ExactOpenScanMember : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code removed k : OrdinaryArithmetic.Term α),
    Nonempty (Derivation B Γ (fromMember r code removed k))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberTargets
