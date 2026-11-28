module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenParentProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxPartsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverAuxSyntaxOpenParentProof (exact_OpenCoverAuxSyntaxParent)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)

/-- A unit syntax hit on a literal auxiliary parent gives the same unit
hit on its function and argument. Same program, same context. -/
theorem exact_OpenUnitAuxSyntaxParts (V TV : Program 1) (B : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (dom cod fn arg : OTerm α)
    (parent : Nonempty (Derivation B Γ
      (unary (unitAuxSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)))) :
    Nonempty (Derivation B Γ (unary (unitAuxSyntax V TV) (suc z) fn)) ∧
    Nonempty (Derivation B Γ (unary (unitAuxSyntax V TV) (suc z) arg)) := by
  have raw := normalizeRecover (auxSyntax V TV) ![auxiliaryTerm dom cod fn arg] parent
  obtain ⟨children⟩ := exact_OpenCoverAuxSyntaxParent V TV B α Γ dom cod fn arg raw
  have parts : Derivation B Γ
      (unary (auxSyntax V TV) (suc z) fn ⊓ unary (auxSyntax V TV) (suc z) arg) :=
    Derivation.conjunctionRight children
  exact ⟨normalizeAccept (auxSyntax V TV) ![fn] ⟨Derivation.conjunctionLeft parts⟩,
    normalizeAccept (auxSyntax V TV) ![arg] ⟨Derivation.conjunctionRight parts⟩⟩

#print axioms exact_OpenUnitAuxSyntaxParts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxPartsProof
