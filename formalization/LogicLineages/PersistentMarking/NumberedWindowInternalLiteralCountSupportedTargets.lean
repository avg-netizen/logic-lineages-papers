module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralCount (allCounts entryCount)

def accepted {α : Type} (code left right : OTerm α) : Formula α :=
  programGraph allCounts (suc z) ![code,left,right]

def counted {α : Type} (list needle result : OTerm α) : Formula α :=
  programGraph entryCount result ![list,needle]

def prem {α : Type} (code left right needle lc rc : OTerm α) : Formula α :=
  accepted code left right ⊓ (memberGraph code needle ⊓ (counted left needle lc ⊓ counted right needle rc))

def query {α : Type} (code left right needle lc rc : OTerm α) : Formula α :=
  (prem code left right needle lc rc).imp (eqn lc rc)

def motive {α : Type} (left right needle lc rc : OTerm α) : Formula (α ⊕ Fin 1) :=
  query (.var (.inr 0)) (left.relabel Sum.inl) (right.relabel Sum.inl) (needle.relabel Sum.inl)
    (lc.relabel Sum.inl) (rc.relabel Sum.inl)

def ExactOpenSupportedCount : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (code left right needle lc rc : OTerm α),
    Nonempty (Derivation B Γ (query code left right needle lc rc))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
