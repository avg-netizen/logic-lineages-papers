module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)

def absentAt {α : Type} (code needle out : OTerm α) : Formula α :=
  ((memberGraph code needle).not ⊓ counted code needle out).imp (eqn out z)

def absentMotive {α : Type} (needle out : OTerm α) : Formula (α ⊕ Fin 1) :=
  absentAt (.var (.inr 0)) (needle.relabel Sum.inl) (out.relabel Sum.inl)

def ExactLiteralAbsentCount : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code needle out : OTerm α),
    Nonempty (Derivation B Γ (absentAt code needle out))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentTargets
