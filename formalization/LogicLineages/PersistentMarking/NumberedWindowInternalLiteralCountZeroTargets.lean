module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)

def zeroAt {α : Type} (code needle : OTerm α) : Formula α :=
  (counted code needle z).imp (memberGraph code needle).not

def zeroMotive {α : Type} (needle : OTerm α) : Formula (α ⊕ Fin 1) :=
  zeroAt (.var (.inr 0)) (needle.relabel Sum.inl)

def ExactLiteralZeroCount : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code needle : OTerm α),
    Nonempty (Derivation B Γ (zeroAt code needle))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroTargets
