module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRefinedPositiveProjectionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRefinedEvenEdgeProjectionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralRefinedScalarTargets (refinedLiteral)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalRefinedPositiveProjectionProof (exact_OriginalRefinedPositiveProjection)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_RefinedEvenCertificateProjects (i : Program 1) (r : Program 3) (c : Nat)
    (x y w : OTerm α)
    (h : Nonempty (Derivation B Γ (certificate (refinedLiteral i r) false c x y w))) :
    Nonempty (Derivation B Γ (certificate (literalData i r) false c x y w)) := by
  have p := (exact_CertificateRules i (jRaw i) (refined i r) (dCore i (refined i r) permutation)
    false c B α Γ x y w).1 h
  exact (exact_CertificateRules i (jRaw i) r (dCore i r permutation) false c B α Γ x y w).2
    (exact_OriginalRefinedPositiveProjection i r ![x,w,y] p)

/-- Refined original even reachability erases only its refinement guards,
in the same ambient ID₁ derivation. It neither moves membership between
bodies nor assumes an earlier source shape. -/
theorem exact_RefinedEvenEdgeProjects (i : Program 1) (r : Program 3) (c : Nat)
    (x y : OTerm α)
    (h : Nonempty (Derivation B Γ (edge (refinedLiteral i r) false c x y))) :
    Nonempty (Derivation B Γ (edge (literalData i r) false c x y)) := by
  obtain ⟨d⟩ := h
  rw [edgeExists] at d
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let q := certificate (refinedLiteral i r) false c (x.relabel Sum.inl) (y.relabel Sum.inl) w
  let Δ := q :: Γ.map weaken
  have read : Derivation B Δ q := Derivation.hypothesis List.mem_cons_self
  have p := exact_RefinedEvenCertificateProjects i r c (x.relabel Sum.inl) (y.relabel Sum.inl) w ⟨read⟩
  obtain ⟨e⟩ := edgeIntroduction p
  apply Nonempty.intro
  apply Derivation.existentialElimination d
  change Derivation B Δ ((edge (literalData i r) false c x y).relabel Sum.inl)
  rw [edgeRename]
  exact e

#print axioms exact_RefinedEvenCertificateProjects
#print axioms exact_RefinedEvenEdgeProjects
end LogicLineages.PersistentMarking.NumberedWindowInternalRefinedEvenEdgeProjectionProof
