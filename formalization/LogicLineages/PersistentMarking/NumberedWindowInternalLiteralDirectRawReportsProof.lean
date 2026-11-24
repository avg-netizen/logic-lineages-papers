module

public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalOneHopInversionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRawReportsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (certificate)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalOriginalOneHopInversionProof (exact_OneHopRawInversionAtReports)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalOriginalFirstHopCoreProof (D)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (direct directData)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- Eliminate the actual original direct certificate and its raw fields.
The report retains the two already-held endpoint addresses, their exact
least values, and the same argument order of the actual raw callback. -/
theorem exact_OpenDirectRawReports (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (c : Nat) (x y ctx ty before after : OTerm α) (goal : Formula α) :
    let data := S i cv tv raw least
    let check := hop cv tv raw least
    let B := sourceBody data c
    D B Γ (addressReport x ctx ty before) →
    D B Γ (addressReport y ctx ty after) →
    D B Γ (direct data check c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (cert src w dst : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (hopCalls raw least (ctx.relabel j) (ty.relabel j) (before.relabel j) cert (after.relabel j) src w dst) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro data check B left right edge use
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let cert := certificate (directData data check) false c (x.relabel j) (y.relabel j) w
  let Δ := cert :: Γ.map weaken
  have keep (f : Formula α) (h : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have bodyCert : D B Δ cert := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ok : D B Δ (accepts check (x.relabel j) w (y.relabel j)) :=
    (exact_CertificateRules i (jRaw i) check (dCore i (addressPositive cv tv raw least) permutation)
      false c B _ Δ (x.relabel j) (y.relabel j) w).1 bodyCert
  have openOk : D B Δ (programGraph check (suc z) ![x.relabel j,w,y.relabel j]) := by
    unfold programGraph accepts at *
    exact ok
  have l := renameInto left j Δ keep
  have r := renameInto right j Δ keep
  rw [addressReportRename] at l r
  have opened := exact_OneHopRawInversionAtReports cv tv raw least (x.relabel j) w (y.relabel j)
    (ctx.relabel j) (ty.relabel j) (before.relabel j) (after.relabel j) l r openOk
  have bridge : D B Δ (goal.relabel j) := by
    apply reportCases raw least (ctx.relabel j) (ty.relabel j) (before.relabel j) w
      (after.relabel j) (goal.relabel j) opened
    intro β k Ω src wit dst stay reports
    let m := k ∘ j
    have both (f : Formula α) (h : f ∈ Γ) : f.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition] using stay _ (keep f h)
    have next := use β m Ω (w.relabel k) src wit dst both
      (by simpa only [m,Term.relabel_relabel] using reports)
    simpa only [m,formulaRelabelComposition] using next
  obtain ⟨step⟩ := bridge
  obtain ⟨some⟩ := edge
  unfold direct at some
  rw [edgeExists] at some
  exact ⟨Derivation.existentialElimination some step⟩

#print axioms exact_OpenDirectRawReports
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRawReportsProof
