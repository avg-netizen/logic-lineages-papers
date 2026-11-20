module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalFreshProbeAlignmentTargets
open NumberedWindowInternalFreshProbeAlignmentProof (align)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)

theorem carriers : ExactGivenFreshAlignmentAndCarriers := by
  intro i j r d p h a c guards total σ τ α Γ q u ht hf
  let S := data i j r d
  let I := sourceBody S c
  obtain ⟨ex⟩ := align S p h a c total σ τ α Γ q u ht hf
  let q' := q.relabel (Sum.inl : α → α ⊕ Fin 1)
  let u' := u.relabel (Sum.inl : α → α ⊕ Fin 1)
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := accepts p q' u' v ⊓ typedAt h τ v
  let Δ := A :: Γ.map weaken
  have pair : Derivation I Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨⟨cq⟩,⟨cu⟩⟩ := guards c I _ Δ q' u' v ⟨Derivation.conjunctionLeft pair⟩
  have both : Nonempty (Derivation I Γ (carrier S false c q ⊓ carrier S false c u)) := by
    apply Nonempty.intro
    apply Derivation.existentialElimination ex
    change Derivation I Δ ((carrier S false c q ⊓ carrier S false c u).relabel Sum.inl)
    simp only [conjunctionRename,carrierRename]
    exact Derivation.conjunctionIntroduction cq cu
  obtain ⟨cl⟩ := both
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft cl)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionRight cl) ex)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
