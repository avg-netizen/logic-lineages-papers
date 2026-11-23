module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanCasesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (scan loopAccept)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalDirectInsertedRowCasesTargets (Reports)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

def FreshCases {α : Type} (Γ : List (Formula α))
    (β : Type) (ρ : α → β) (Δ : List (Formula β)) : Prop :=
  ∀ p ∈ Γ, p.relabel ρ ∈ Δ

def parseReport {α : Type} (inserted decoded : OrdinaryArithmetic.Term α) : Formula α :=
  unary parser (OrdinaryArithmetic.succTerm decoded) inserted

/-- Acceptance opens the actual parsed inserted tape and its accepting loop,
without supplying a held parser hypothesis. -/
def ExactOpenScanCases : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (inserted removed : OrdinaryArithmetic.Term α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph (scan r) oneTerm ![inserted,removed])) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (decoded : OrdinaryArithmetic.Term β),
      FreshCases Γ β ρ Δ →
      Nonempty (Derivation B Δ (parseReport (inserted.relabel ρ) decoded)) →
      Nonempty (Derivation B Δ (loopAccept r decoded (removed.relabel ρ))) →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal)

/-- With actual object membership in the selected inserted scratch tape,
open the accepted member's original row reports. The removed tape never
changes; one removed parser witness is shared by its parser and dominator
reports. This does not assert occurrence at a particular index or that an
arbitrary term is a member. -/
def ExactOpenScanMemberCases : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (inserted removed row : OrdinaryArithmetic.Term α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph (scan r) oneTerm ![inserted,removed])) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (decoded : OrdinaryArithmetic.Term β),
      FreshCases Γ β ρ Δ →
      Nonempty (Derivation B Δ (parseReport (inserted.relabel ρ) decoded)) →
      Nonempty (Derivation B Δ (memberGraph decoded (row.relabel ρ)))) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β))
        (decoded removedCode target dom cert : OrdinaryArithmetic.Term β),
      FreshCases Γ β ρ Δ →
      Nonempty (Derivation B Δ (parseReport (inserted.relabel ρ) decoded)) →
      Nonempty (Derivation B Δ (memberGraph decoded (row.relabel ρ))) →
      Reports r B Δ (removed.relabel ρ) (row.relabel ρ) removedCode target dom cert →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanCasesTargets
