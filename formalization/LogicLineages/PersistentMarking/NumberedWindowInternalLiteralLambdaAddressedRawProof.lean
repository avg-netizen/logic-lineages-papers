module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaCanonicalHeaderProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalUnderlyingReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaAddressedRawProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalLiteralLambdaCanonicalHeaderProof (exact_OpenCanonicalLambdaHeader)
open NumberedWindowInternalLiteralLeastReflectsHeaderProof (exact_OpenGuardedLeastReflectsHeader)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralNeutralAtomProof (lambdaHeader)
open NumberedWindowInternalNeutralFactsTargets (atom direct)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralPhysicalUnderlyingReportsProof (exact_OpenPhysicalUnderlyingReports)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- Open an actual direct step at an originally recognized canonical
lambda address. The source header is recovered at the original raw
representative of the real certificate, with every checked tape and
the exact addressed destination retained. -/
theorem exact_OpenLambdaAddressedRaw (i cv tv : Program 1) (raw : Program 5) (pre : Program 3)
    (c : Nat) (x y : OTerm α) (goal : Formula α) :
    let L := guardedLeast (headerLeast pre)
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let H := hop cv tv R L
    let B := sourceBody data c
    D B Γ (atom lambdaHeader x) → D B Γ (direct data H c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (ctx ty before after cert q w r : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (addressReport (x.relabel j) ctx ty before) →
      D B Δ (addressReport (y.relabel j) ctx ty after) →
      D B Δ (unary cv (suc z) ctx) → D B Δ (unary tv (suc z) ty) →
      D B Δ (carrier data false c (y.relabel j)) →
      D B Δ (unary cellHead (numeral 2) q) →
      D B Δ (hopCalls raw L ctx ty before cert after q w r) → D B Δ (goal.relabel j)) →
    D B Γ goal := by
  intro L R data H B shape directStep use
  apply exact_OpenPhysicalUnderlyingReports i cv tv raw L c x y goal directStep
  intro β j Δ ctx ty before after cert q w r keep start finish gc gt carrier calls
  have lambda := renameInto shape j Δ keep
  rw [atomRename] at lambda
  have atMin := exact_OpenCanonicalLambdaHeader (x.relabel j) ctx ty before lambda start
  obtain ⟨row⟩ := calls
  have atRaw := exact_OpenGuardedLeastReflectsHeader pre ctx ty q before (numeral 2)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight row))⟩ atMin
  exact use β j Δ ctx ty before after cert q w r keep start finish gc gt carrier atRaw ⟨row⟩

#print axioms exact_OpenLambdaAddressedRaw
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaAddressedRawProof
