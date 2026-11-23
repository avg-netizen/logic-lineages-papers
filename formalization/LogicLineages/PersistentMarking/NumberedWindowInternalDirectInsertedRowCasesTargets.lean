module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedRowTargets (insertedRow oneTerm)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (tripleTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

structure Reports (r : Program 3) (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (removed row decoded target dom cert : OrdinaryArithmetic.Term α) : Prop where
  parsed : Nonempty (Derivation B Γ (unary parser (OrdinaryArithmetic.succTerm decoded) removed))
  targetField : Nonempty (Derivation B Γ (unary (field 0) target row))
  dominatorField : Nonempty (Derivation B Γ (unary (field 1) dom row))
  certificateField : Nonempty (Derivation B Γ (unary (field 2) cert row))
  original : Nonempty (Derivation B Γ
    (equal row (tripleTerm 4 target dom cert) ⊓
      (programGraph scratchMember oneTerm ![decoded,dom] ⊓
        programGraph r oneTerm ![dom,cert,target])))

/-- Unconditional object witness elimination from the actual selected row.
The reports are available only inside the strengthened object context of the
original object-calculus existential eliminators; no ambient code choices. -/
def ExactOpenInsertedRowCases : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (removed row : OrdinaryArithmetic.Term α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph (insertedRow r) oneTerm ![removed,row])) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β))
        (decoded target dom cert : OrdinaryArithmetic.Term β),
      (∀ p ∈ Γ, p.relabel ρ ∈ Δ) →
      Reports r B Δ (removed.relabel ρ) (row.relabel ρ) decoded target dom cert →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesTargets
