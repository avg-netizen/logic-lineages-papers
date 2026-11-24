module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonInverseProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEndpointSingletonProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalScalarSingletonInductionProof (singletonJ)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalLiteralSingletonInverseProof
  (ScalarEdgeTargetsCarry exact_LiteralSingletonMembershipEquivalence)
open NumberedWindowInternalLiteralSingletonCarrierReflectionProof (D)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementObjectChecks
  (exact_OriginalPositiveCertificateEndpointCarriers)

/-- The actual same literal body recovers both scalar carriers from
the guarded original edge, even when its certificate is existential. -/
theorem exact_EndpointRefinedLiteralEdgeCarriers (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x y : OTerm α) :
    let R := withEndpointCarriers i r
    let S := literalData i R
    let B := sourceBody S c
    D B Γ (edge S false c x y) → D B Γ (carrier S false c x ⊓ carrier S false c y) := by
  dsimp only
  intro accepted
  let R := withEndpointCarriers i r
  let S := literalData i R
  let B := sourceBody S c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := certificate S false c (x.relabel j) (y.relabel j) w
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  obtain ⟨h⟩ := exact_OriginalPositiveCertificateEndpointCarriers i (jRaw i) r (dCore i R permutation)
    c _ Δ (x.relabel j) w (y.relabel j) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have pair : Derivation B Δ (weaken (carrier S false c x ⊓ carrier S false c y)) := by
    simp only [weaken,ID1Completion.InternalRecursionGraphStepSyntaxProof.conjunctionRename,carrierRename]
    exact Derivation.conjunctionRight h
  obtain ⟨e⟩ := accepted
  rw [edgeExists] at e
  exact ⟨Derivation.existentialElimination e pair⟩

/-- No endpoint proof is needed from the consumer once the actual
positive callback includes the original scalar endpoint guards. -/
theorem exact_EndpointRefinedLiteralSingletonIff (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (q : OTerm α) :
    let R := withEndpointCarriers i r
    let B := sourceBody (literalData i R) c
    D B Γ (singletonJ q) ↔ D B Γ (membership false q) := by
  let R := withEndpointCarriers i r
  have target : ScalarEdgeTargetsCarry i R c := by
    intro β Δ x y edge
    obtain ⟨both⟩ := exact_EndpointRefinedLiteralEdgeCarriers i r c β Δ x y edge
    exact ⟨Derivation.conjunctionRight both⟩
  exact exact_LiteralSingletonMembershipEquivalence i R c target α Γ q

#print axioms exact_EndpointRefinedLiteralEdgeCarriers
#print axioms exact_EndpointRefinedLiteralSingletonIff
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEndpointSingletonProof
