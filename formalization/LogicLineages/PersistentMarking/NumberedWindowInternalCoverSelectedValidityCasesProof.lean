module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityCasesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (moveReport)
open NumberedWindowInternalCoverSelectedValidityTargets
open NumberedWindowInternalCoverSelectedValidityOpenProof (exact_OpenCoverSelectedValidityHeaders)
open NumberedWindowInternalCoverHeaderFieldsOpenProof (exact_OpenCoverHeaderFields)
open NumberedWindowInternalCoverSelectedValidityCasesTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Eliminate the physical header disjunction once, preserving original
validity and reselected validity across every fresh field binder. -/
private theorem eliminateHeaders (V : Program 1) (xs : List (Nat × Nat)) (q : OTerm α)
    (goal : Formula α)
    (old : Nonempty (Derivation body Γ (unary V (suc z) q)))
    (selected : Nonempty (Derivation body Γ (unary (selectedValidity V) (suc z) q)))
    (rows : Nonempty (Derivation body Γ (headersAt xs q)))
    (branch : ValidBranchCase xs V body Γ q goal) :
    Nonempty (Derivation body Γ goal) := by
  induction xs generalizing Γ with
  | nil =>
    obtain ⟨bad⟩ := rows
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  | cons pair rest ih =>
    obtain ⟨tag,arity⟩ := pair
    let A := headerAt tag arity q
    let B := headersAt rest q
    have here : Nonempty (Derivation body (A :: Γ) goal) := by
      have good : Nonempty (Derivation body (A :: Γ) (headerAt tag arity q)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply exact_OpenCoverHeaderFields tag arity body α (A :: Γ) q goal good
      intro β j Δ fields keep len reports eq
      have nextKeep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
        keep p (List.mem_cons_of_mem _ hp)
      have hd := moveReport j Δ keep (header tag arity) (suc z) q good
      have old' := moveReport j Δ nextKeep V (suc z) q old
      have selected' := moveReport j Δ nextKeep (selectedValidity V) (suc z) q selected
      simp only [sucRelabel,zRelabel] at hd old' selected'
      exact branch tag arity List.mem_cons_self β j Δ fields nextKeep len reports eq hd old' selected'
    have later : Nonempty (Derivation body (B :: Γ) goal) := by
      apply ih (withHyp old B) (withHyp selected B) ⟨Derivation.hypothesis List.mem_cons_self⟩
      intro t a hit β j Δ fields keep len reports eq hd o s
      have nextKeep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
        keep p (List.mem_cons_of_mem _ hp)
      exact branch t a (List.mem_cons_of_mem _ hit) β j Δ fields nextKeep len reports eq hd o s
    obtain ⟨rows⟩ := rows
    obtain ⟨here⟩ := here
    obtain ⟨later⟩ := later
    exact ⟨disjunctionElimination rows (Derivation.implicationIntroduction here)
      (Derivation.implicationIntroduction later)⟩

theorem exact_OpenCoverSelectedValidityCases : ExactOpenCoverSelectedValidityCases := by
  intro V body α Γ q goal selectedCases next
  obtain ⟨both⟩ := exact_OpenCoverSelectedValidityHeaders V body α Γ q selectedCases
  exact eliminateHeaders V layout q goal ⟨Derivation.conjunctionLeft both⟩ selectedCases
    ⟨Derivation.conjunctionRight both⟩ next

#print axioms exact_OpenCoverSelectedValidityCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityCasesProof
