module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralReportedAuxiliaryProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectCarrierInstalledProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredCarrierReportsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralDirectRawReportsProof (exact_OpenDirectRawReports)
open NumberedWindowInternalLiteralDirectTargetCarrierProof (exact_OpenDirectTargetCarrier)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget targetGate)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The new raw wrapper contains the actual old checker, on exactly
the same five inputs. Removing the guard in this direction does not
identify either the installed presentations or their proof trees. -/
theorem exact_OpenUnderlyingHopCalls (i cv tv : Program 1) (R : Program 5) (L : Program 3)
    (ctx ty before cert after q w r : OTerm α)
    (held : D B Γ (hopCalls (rawWithTarget i cv tv R L) L ctx ty before cert after q w r)) :
    D B Γ (hopCalls R L ctx ty before cert after q w r) := by
  obtain ⟨row⟩ := held
  let calls := Derivation.conjunctionRight row
  have raw : D B Γ (programGraph (rawWithTarget i cv tv R L) (suc z) ![ctx,ty,q,w,r]) :=
    ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨selected⟩ := conjunctionRecover R (targetGate i cv tv L) ![ctx,ty,q,w,r] raw
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft row)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft selected) (Derivation.conjunctionRight calls))⟩

/-- The exact original reports, including the underlying raw step and
both successful least queries, and the checked target scalar carrier
are available together in an arbitrary context of one installed body. -/
theorem exact_OpenDirectCarrierAndUnderlyingReports (i cv tv : Program 1) (R : Program 5)
    (L : Program 3) (c : Nat) (x y ctx ty before after : OTerm α) (goal : Formula α) :
    let raw := rawWithTarget i cv tv R L
    let data := S i cv tv raw L
    let B := sourceBody data c
    D B Γ (addressReport x ctx ty before) →
    D B Γ (addressReport y ctx ty after) →
    D B Γ (direct data (hop cv tv raw L) c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (cert q w r : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (carrier data false c (y.relabel j)) →
      D B Δ (hopCalls R L (ctx.relabel j) (ty.relabel j) (before.relabel j) cert (after.relabel j) q w r) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro raw data B left right step use
  have target := exact_OpenDirectTargetCarrier i cv tv R L c x y step
  apply exact_OpenDirectRawReports i cv tv raw L c x y ctx ty before after goal left right step
  intro β j Δ cert q w r keep report
  have carried := renameInto target j Δ keep
  rw [carrierRename] at carried
  exact use β j Δ cert q w r keep carried
    (exact_OpenUnderlyingHopCalls i cv tv R L _ _ _ _ _ _ _ _ report)

#print axioms exact_OpenUnderlyingHopCalls
#print axioms exact_OpenDirectCarrierAndUnderlyingReports
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredCarrierReportsProof
