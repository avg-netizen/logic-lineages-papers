module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenIntroProof
public import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeRecover)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverAuxSyntaxNumericProof (exact_CoverAuxSyntaxCalibration)
open NumberedWindowInternalCoverAuxSyntaxOpenIntroProof (exact_OpenCoverAuxSyntaxIntro)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

abbrev unitAuxSyntax (V TV : Program 1) : Program 1 := normalize (auxSyntax V TV)

theorem exact_LiteralUnitAuxSyntax (V TV : Program 1)
    (raw : TermSyntaxCalibrated V)
    (ty : NumberedWindowInternalCoverLambdaSyntaxRowTargets.TypeSyntaxCalibrated TV) :
    TermSyntaxCalibrated (unitAuxSyntax V TV) := by
  intro q
  unfold unitAuxSyntax run
  rw [GorbowVerifierNormalization.Proof.actualEvaluation.2,
    show evaluate (auxSyntax V TV) (List.Vector.cons q List.Vector.nil) =
      ((syntaxBits q).1).toNat from exact_CoverAuxSyntaxCalibration V TV raw ty q]
  cases (syntaxBits q).1 <;> rfl

/-- A successful unit syntax check on each actual child pays the same
selected unit check at the original literal auxiliary parent. -/
theorem exact_OpenUnitAuxSyntaxIntro (V TV : Program 1) (B : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (dom cod fn arg : OTerm α)
    (d : Nonempty (Derivation B Γ (unary TV (suc z) dom)))
    (c : Nonempty (Derivation B Γ (unary TV (suc z) cod)))
    (f : Nonempty (Derivation B Γ (unary (unitAuxSyntax V TV) (suc z) fn)))
    (a : Nonempty (Derivation B Γ (unary (unitAuxSyntax V TV) (suc z) arg))) :
    Nonempty (Derivation B Γ (unary (unitAuxSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg))) := by
  obtain ⟨d⟩ := d
  obtain ⟨c⟩ := c
  obtain ⟨rf⟩ := normalizeRecover (auxSyntax V TV) ![fn] f
  obtain ⟨ra⟩ := normalizeRecover (auxSyntax V TV) ![arg] a
  have valid := exact_OpenCoverAuxSyntaxIntro V TV B α Γ dom cod fn arg
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction d c)
      (Derivation.conjunctionIntroduction rf ra)⟩
  exact normalizeAccept (auxSyntax V TV) ![auxiliaryTerm dom cod fn arg] valid

#print axioms exact_LiteralUnitAuxSyntax
#print axioms exact_OpenUnitAuxSyntaxIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
