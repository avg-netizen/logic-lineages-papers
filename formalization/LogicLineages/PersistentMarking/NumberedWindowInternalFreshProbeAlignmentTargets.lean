module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
public import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source (Ty)
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalProbeTargets (OTerm typedAt freshAt TypedProbeTotal)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowGuardedGraphTargets (InputGuards)

/-- Only the result is bound. The given original source and already
selected fresh argument survive as the free q/u in this one block. -/
def alignedResultAt {α : Type} (p : Program 3) (h : Program 2)
    (τ : Ty) (q u : OTerm α) : Formula α :=
  let q' := q.relabel (Sum.inl : α → α ⊕ Fin 1)
  let u' := u.relabel (Sum.inl : α → α ⊕ Fin 1)
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (accepts p q' u' v ⊓ typedAt h τ v)

def AlignedAt (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat) : Prop :=
  ∀ (σ τ : Ty) (α : Type) (Γ : List (Formula α)) (q u : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (typedAt h (.arrow σ τ) q)) →
    Nonempty (Derivation (sourceBody d c) Γ (freshAt a q u)) →
    Nonempty (Derivation (sourceBody d c) Γ (alignedResultAt p h τ q u))

/-- Actual given fresh argument u, not just some new u from totality.
The actual h also types this result at the same requested codomain. -/
def ExactGivenFreshProbeAlignment : Prop :=
  ∀ (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat),
    TypedProbeTotal d p h a c → AlignedAt d p h a c

def AlignedCarriersAt (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat) : Prop :=
  ∀ (σ τ : Ty) (α : Type) (Γ : List (Formula α)) (q u : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (typedAt h (.arrow σ τ) q)) →
    Nonempty (Derivation (sourceBody d c) Γ (freshAt a q u)) →
    Nonempty (Derivation (sourceBody d c) Γ
      (carrier d false c q ⊓ (carrier d false c u ⊓ alignedResultAt p h τ q u)))

/-- The same concrete p and the original input guard yield both scalar
carriers. This does not assert typedness at u, I-membership, lexical
canonicality, or computability of u. -/
def ExactGivenFreshAlignmentAndCarriers : Prop :=
  ∀ (i j : Program 1) (r d p : Program 3) (h : Program 2) (a : Program 1) (c : Nat),
    InputGuards i j r d p → TypedProbeTotal (data i j r d) p h a c →
    AlignedCarriersAt (data i j r d) p h a c

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentTargets
