module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectPhysicalReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectTargetCarrierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalUnderlyingReportsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalOriginalFirstHopCoreProof (D)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget targetGate)
open NumberedWindowInternalLiteralDirectTargetCarrierProof (exact_OpenDirectTargetCarrier)
open NumberedWindowInternalLiteralDirectPhysicalReportProof (exact_OpenDirectPhysicalReportCases)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem underlyingCalls (i cv tv : Program 1) (raw : Program 5) (L : Program 3)
    (ctx ty before cert after q w r : OTerm α)
    (held : D B Γ (hopCalls (rawWithTarget i cv tv raw L) L ctx ty before cert after q w r)) :
    D B Γ (hopCalls raw L ctx ty before cert after q w r) := by
  obtain ⟨row⟩ := held
  let calls := Derivation.conjunctionRight row
  have gate : D B Γ (programGraph (rawWithTarget i cv tv raw L) (suc z) ![ctx,ty,q,w,r]) :=
    ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨selected⟩ := conjunctionRecover raw (targetGate i cv tv L) ![ctx,ty,q,w,r] gate
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft row)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft selected)
      (Derivation.conjunctionRight calls))⟩

/-- Inspect a physical direct edge in its own installed body. In one
open context, the continuation receives both endpoints and validators,
the target carrier, and the actual old raw call with both least queries.
The target gate may be projected away only inside the callback report;
the direct edge and every derivation stay on the original installed body. -/
theorem exact_OpenPhysicalUnderlyingReports (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x y : OTerm α) (goal : Formula α) :
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (direct data (hop cv tv R L) c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (ctx ty before after cert q w r : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (addressReport (x.relabel j) ctx ty before) →
      D B Δ (addressReport (y.relabel j) ctx ty after) →
      D B Δ (unary cv (suc z) ctx) → D B Δ (unary tv (suc z) ty) →
      D B Δ (carrier data false c (y.relabel j)) →
      D B Δ (hopCalls raw L ctx ty before cert after q w r) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro R data B edge use
  have target := exact_OpenDirectTargetCarrier i cv tv raw L c x y edge
  apply exact_OpenDirectPhysicalReportCases i cv tv R L c x y goal edge
  intro β j Δ cert ctx ty before after keep hx hy pc pt calls
  apply reportCases R L ctx ty before cert after (goal.relabel j) calls
  intro γ k Ω q w r stay report
  let m := k ∘ j
  have retain (f : Formula α) (hf : f ∈ Γ) : f.relabel m ∈ Ω := by
    simpa only [m,formulaRelabelComposition] using stay _ (keep f hf)
  have left := renameInto hx k Ω stay
  have right := renameInto hy k Ω stay
  rw [addressReportRename] at left right
  have context := renameInto pc k Ω stay
  have type := renameInto pt k Ω stay
  simp only [unaryRename,sucRelabel,zRelabel] at context type
  have carried := renameInto target m Ω retain
  rw [carrierRename] at carried
  have finish := use γ m Ω (ctx.relabel k) (ty.relabel k) (before.relabel k) (after.relabel k)
    (cert.relabel k) q w r retain
    (by simpa only [m,Term.relabel_relabel] using left)
    (by simpa only [m,Term.relabel_relabel] using right)
    context type carried (underlyingCalls i cv tv raw L _ _ _ _ _ _ _ _ report)
  simpa only [m,formulaRelabelComposition] using finish

#print axioms exact_OpenPhysicalUnderlyingReports
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalUnderlyingReportsProof
