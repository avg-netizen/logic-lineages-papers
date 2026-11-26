module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm namedReport)

abbrev originRow {α : Type} (isBound : Bool) (K m key ty i : OTerm α) : Formula α :=
  memberGraph K ty ⊓ (ltF i (suc m) ⊓ eqn (namedTerm isBound.toNat ty i) key)

abbrev originMatrix {α : Type} (isBound : Bool) (K m key : OTerm α) : Formula (α ⊕ Fin 2) :=
  originRow isBound (K.relabel Sum.inl) (m.relabel Sum.inl) (key.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))

def namedOrigin {α : Type} (isBound : Bool) (K m key : OTerm α) : Formula α :=
  block (originMatrix isBound K m key)

/-- The two sources of this actual named key are the original type list
and original inclusive numeral range. The equality is object arithmetic
for the physical sparse tag/type/index code. -/
def ExactOpenCoverNamedLeafOrigin : Prop :=
  ∀ (isBound : Bool) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out K m key : OTerm α),
  Nonempty (Derivation body Γ (namedReport isBound out K m)) →
  Nonempty (Derivation body Γ (memberGraph out key)) →
  Nonempty (Derivation body Γ (namedOrigin isBound K m key))

/-- Transport an existing actual named leaf occurrence to an actual
larger-bound report for the same original type list and tag, without
changing its sparse key. This is only the named-leaf component. -/
def ExactOpenCoverNamedLeafTransport : Prop :=
  ∀ (isBound : Bool) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (old next K m M key : OTerm α),
  Nonempty (Derivation body Γ (namedReport isBound old K m)) →
  Nonempty (Derivation body Γ (memberGraph old key)) →
  Nonempty (Derivation body Γ (ltF m (suc M))) →
  Nonempty (Derivation body Γ (namedReport isBound next K M)) →
  Nonempty (Derivation body Γ (memberGraph next key))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginTargets
