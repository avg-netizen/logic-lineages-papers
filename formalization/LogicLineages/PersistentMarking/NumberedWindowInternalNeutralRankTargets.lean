module

public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open SourceComputabilityFormulaSupportProof (allOne)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalStrongInduction (below)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)

def positiveRank {α : Type} (g : Program 1) (k x : OTerm α) : Formula α :=
  unary g (suc k) x

/-- For an actual original edge, open the actual successor's positive
rank report and carrier at this same y. The rank bound is true object
arithmetic on the actual predecessor coordinate, not a host inequality.
No accessibility assertion is part of the interface. -/
def RankDrop (S : Data) (g : Program 1) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (k x y : OTerm α) (goal : Formula α),
    Nonempty (Derivation (sourceBody S c) Γ (edge S false c x y)) →
    Nonempty (Derivation (sourceBody S c) Γ (positiveRank g k x)) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      Nonempty (Derivation (sourceBody S c) Δ (carrier S false c (y.relabel ρ))) →
      Nonempty (Derivation (sourceBody S c) Δ (positiveRank g j (y.relabel ρ))) →
      Nonempty (Derivation (sourceBody S c) Δ (ltF j (k.relabel ρ))) →
      Nonempty (Derivation (sourceBody S c) Δ (goal.relabel ρ))) →
    Nonempty (Derivation (sourceBody S c) Γ goal)

def rankClause {α : Type} (S : Data) (g : Program 1) (c : Nat) (k x : OTerm α) : Formula α :=
  (carrier S false c x ⊓ positiveRank g k x).imp (membership false x)

def rankMatrix {α : Type} (S : Data) (g : Program 1) (c : Nat) (k : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  rankClause S g c (k.relabel Sum.inl) (.var (.inr 0))

def rankFamily {α : Type} (S : Data) (g : Program 1) (c : Nat) (k : OTerm α) : Formula α :=
  allOne (rankMatrix S g c k)

def rankMotive {α : Type} (S : Data) (g : Program 1) (c : Nat) : Formula (α ⊕ Fin 1) :=
  rankFamily S g c (.var (.inr 0))

def lowerRanks {α : Type} (S : Data) (g : Program 1) (c : Nat) (k : OTerm α) : Formula α :=
  below (rankMotive S g c) k

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankTargets
