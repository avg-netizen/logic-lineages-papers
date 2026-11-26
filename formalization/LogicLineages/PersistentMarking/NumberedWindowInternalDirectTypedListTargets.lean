module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryGuardsTargets
public import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalEqualityTest (predecessor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch ScalarFit)
open NumberedWindowDirectAlgorithm (typedList)

def parsedPayload : Program 1 := .composition predecessor (Fin.cons parser Fin.elim0)
def typedPayload (i : Program 1) : Program 1 :=
  .composition (typedScratch i) (Fin.cons parsedPayload Fin.elim0)

/-- Actual original raw list parser, no nonempty test. A parsed empty code
passes through its positive parser result to the vacuous scalar fold. -/
def jRaw (i : Program 1) : Program 1 := branch parser (constantZero 1) (typedPayload i)

def ExactNumericJRaw : Prop :=
  ∀ (i : Program 1) (scalar : Nat → Bool), ScalarFit i scalar →
    ∀ raw, evaluate (jRaw i) (raw ::ᵥ nil) = (typedList scalar raw).toNat

structure Reports (i : Program 1) (B : Positive (Fin 1)) {α : Type}
    (Γ : List (Formula α)) (raw decoded : OTerm α) : Prop where
  parsed : Nonempty (Derivation B Γ (unary parser (suc decoded) raw))
  typed : Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) decoded))

def ExactOpenJRaw : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (unary (jRaw i) (suc z) raw)) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (decoded : OTerm β),
      (∀ p ∈ Γ, p.relabel ρ ∈ Δ) → Reports i B Δ (raw.relabel ρ) decoded →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal)

def ExactIntroJRaw : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw decoded : OTerm α), Reports i B Γ raw decoded →
    Nonempty (Derivation B Γ (unary (jRaw i) (suc z) raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListTargets
