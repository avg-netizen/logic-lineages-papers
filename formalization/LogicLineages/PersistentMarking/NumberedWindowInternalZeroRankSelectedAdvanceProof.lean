module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceObjectProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastReflectProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankSelectedAdvanceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceChecks (exact_OpenSuccessfulAdvanceCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalZeroRankAdvanceObjectProof (exact_OpenZeroRankOutput)
open NumberedWindowInternalRankCheckedLeast (checkedLeast)
open NumberedWindowInternalRankCheckedLeastReportsProof (exact_OpenRankCheckedLeastReports)
open NumberedWindowInternalRankCheckedLeastReflectProof (exact_OpenRankCheckedLeastReflect)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Actual positive zero-output filtered original advance. The unchanged
hop and both genuine checked/old least reports use the exact same
physical q,w,r and caller coordinates. -/
theorem exact_OpenZeroRankSelectedAdvance
    (g : Program 1) (raw : Program 5) (L : Program 3) (ctx ty current hop target : OTerm α)
    (goal : Formula α)
    (selected : Nonempty (Derivation B Γ
      (programGraph (zeroOutput g (advance raw (checkedLeast g L))) (suc target) ![ctx,ty,suc current,hop])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (hopCalls raw (checkedLeast g L) (ctx.relabel j) (ty.relabel j)
        (current.relabel j) (hop.relabel j) (target.relabel j) q w r)) →
      Nonempty (Derivation B Δ (hopCalls raw L (ctx.relabel j) (ty.relabel j)
        (current.relabel j) (hop.relabel j) (target.relabel j) q w r)) →
      Nonempty (Derivation B Δ (unary g z (target.relabel j))) →
      Nonempty (Derivation B Δ (unary g z r)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  let L' := checkedLeast g L
  obtain ⟨found⟩ := exact_OpenZeroRankOutput g (advance raw L') ![ctx,ty,suc current,hop] target selected
  let rankTarget : Nonempty (Derivation B Γ (unary g z target)) :=
    ⟨Derivation.conjunctionRight found⟩
  obtain ⟨rule⟩ := exact_OpenSuccessfulAdvanceCalls B raw L' α ctx ty current hop target
  have reports := Derivation.implicationElimination (weakenClosed (Derivation.conjunctionLeft rule) Γ)
    (Derivation.conjunctionLeft found)
  apply reportCases raw L' ctx ty current hop target goal ⟨reports⟩
  intro β j Δ q w r keep checks
  obtain ⟨hit⟩ := checks
  let c := ctx.relabel j
  let t := ty.relabel j
  let f := current.relabel j
  let f' := target.relabel j
  let graphRow := Derivation.conjunctionRight hit
  let leasts := Derivation.conjunctionRight graphRow
  have src : Nonempty (Derivation B Δ (programGraph L' (suc f) ![c,t,q])) :=
    ⟨Derivation.conjunctionLeft leasts⟩
  have dst : Nonempty (Derivation B Δ (programGraph L' (suc f') ![c,t,r])) :=
    ⟨Derivation.conjunctionRight leasts⟩
  obtain ⟨oldSrc⟩ := exact_OpenRankCheckedLeastReports g L c t q f src
  obtain ⟨oldDst⟩ := exact_OpenRankCheckedLeastReports g L c t r f' dst
  have targetZero := renameInto rankTarget j Δ keep
  rw [unaryRename,zRelabel] at targetZero
  have rawZero := exact_OpenRankCheckedLeastReflect g L c t r f' z dst targetZero
  have oldCalls : Nonempty (Derivation B Δ (hopCalls raw L c t f (hop.relabel j) f' q w r)) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hit)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft graphRow)
        (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft oldSrc)
          (Derivation.conjunctionLeft oldDst)))⟩
  exact next β j Δ q w r keep ⟨hit⟩ oldCalls targetZero rawZero

/-- An actual zero rank of the caller's given current k additionally
pays zero rank of the actual parsed source q. The output-only filter
alone does not pay this extra source premise. -/
theorem exact_OpenZeroRankSelectedAdvanceBoth
    (g : Program 1) (raw : Program 5) (L : Program 3) (ctx ty current hop target : OTerm α)
    (goal : Formula α)
    (sourceZero : Nonempty (Derivation B Γ (unary g z current)))
    (selected : Nonempty (Derivation B Γ
      (programGraph (zeroOutput g (advance raw (checkedLeast g L))) (suc target) ![ctx,ty,suc current,hop])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (hopCalls raw L (ctx.relabel j) (ty.relabel j)
        (current.relabel j) (hop.relabel j) (target.relabel j) q w r)) →
      Nonempty (Derivation B Δ (unary g z q)) →
      Nonempty (Derivation B Δ (unary g z r)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply exact_OpenZeroRankSelectedAdvance g raw L ctx ty current hop target goal selected
  intro β j Δ q w r keep newCalls oldCalls _ rawR
  obtain ⟨h⟩ := newCalls
  have onCurrent := renameInto sourceZero j Δ keep
  rw [unaryRename,zRelabel] at onCurrent
  have src : Nonempty (Derivation B Δ (programGraph (checkedLeast g L) (suc (current.relabel j))
      ![ctx.relabel j,ty.relabel j,q])) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight h))⟩
  have rawQ := exact_OpenRankCheckedLeastReflect g L (ctx.relabel j) (ty.relabel j) q
    (current.relabel j) z src onCurrent
  exact next β j Δ q w r keep oldCalls rawQ rawR

#print axioms exact_OpenZeroRankSelectedAdvance
#print axioms exact_OpenZeroRankSelectedAdvanceBoth
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankSelectedAdvanceProof
