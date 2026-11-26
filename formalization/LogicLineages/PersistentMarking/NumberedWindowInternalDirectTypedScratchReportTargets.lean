module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryGuardsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchReportTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalDirectBoundaryGuardsTargets (normalizeScalar typedScratch)
open ID1Completion.InternalListMap (map)

abbrev normalizedMap (i : Program 1) : Program 1 := map (k := 0) (normalizeScalar i)

structure Reports (i : Program 1) (B : Positive (Fin 1)) {α : Type}
    (Γ : List (Formula α)) (code mapped : OTerm α) : Prop where
  mappedCall : Nonempty (Derivation B Γ (unary (normalizedMap i) mapped code))
  missingZero : Nonempty (Derivation B Γ (programGraph scratchMember z ![mapped,z]))

def ExactEliminateTypedScratch : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) code)) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (mapped : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) → Reports i B Δ (code.relabel ρ) mapped →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal)

def ExactIntroduceTypedScratch : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code mapped : OTerm α), Reports i B Γ code mapped →
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) code))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchReportTargets
