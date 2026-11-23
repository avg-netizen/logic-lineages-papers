module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRefitTypeSyntaxProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptance (conjunction)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalAuxWindowMemoTargets (typeGuard IntrinsicWindowCalibrated selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowStepChecks (exact_PhysicalAuxWindow)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow ActualRawSyntax)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalSettingsGrammarGuardNumericProof (exact_SettingsRefitGuardCalibration)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (WindowSeedsCovered syntaxWindow window)
open NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof
  (exact_SyntaxWindowCalibration exact_LiteralCoveredWindowCalibration)

/-- The original grammar membership guard and same selected unary TV
are physically present, not recovered by numerical reflection. -/
def refitTypeSyntax (s : Settings) (T TV : Program 1) : Program 1 :=
  conjunction (refitGuard s T) TV

theorem exact_OriginalRefitTypeSyntaxGuard (s : Settings) (T TV : Program 1)
    (included : GrammarTypeInclusion s) (original : TypeGuardCalibrated s T)
    (types : TypeSyntaxCalibrated TV) :
    TypeGuardCalibrated s (refitTypeSyntax s T TV) := by
  intro ty
  have refit : evaluate (refitGuard s T) (ty ::ᵥ nil) = (typeGuard s ty).toNat :=
    exact_SettingsRefitGuardCalibration s T included original ty
  have syntaxValue : evaluate TV (ty ::ᵥ nil) = (typeBit ty).toNat := types ty
  change evaluate (conjunction (refitGuard s T) TV) (ty ::ᵥ nil) = (typeGuard s ty).toNat
  rw [actualConjunctionEvaluation,refit,syntaxValue]
  cases old : typeGuard s ty with
  | false => simp
  | true =>
    have both : (typeBit ty && s.window.1.contains ty) = true := old
    have typeYes := (Bool.and_eq_true_iff.mp both).1
    simp [typeYes]

/-- Keep the literal intrinsic base callback and reselect its physical
auxiliary recursion at the new calibrated guard. -/
theorem exact_OriginalRefitTypeSyntaxWindow (s : Settings) (base : Program 2) (T TV : Program 1)
    (included : GrammarTypeInclusion s) (baseFit : IntrinsicWindowCalibrated s base)
    (original : TypeGuardCalibrated s T) (types : TypeSyntaxCalibrated TV) :
    ActualPackedWindow s (intrinsicQuery (selectedIntrinsic (windowUpdate base (refitTypeSyntax s T TV)))) :=
  exact_PhysicalAuxWindow s base (refitTypeSyntax s T TV) baseFit
    (exact_OriginalRefitTypeSyntaxGuard s T TV included original types)

/-- Preserve the full literal own-cover + Va wrapper on all input tapes.
No held report of the old packed window is reused on the new physical Wp. -/
theorem exact_OriginalRefitTypeSyntaxCoveredWindow (s : Settings) (base : Program 2) (T TV Va : Program 1)
    (C : Program 3) (included : GrammarTypeInclusion s) (baseFit : IntrinsicWindowCalibrated s base)
    (original : TypeGuardCalibrated s T) (types : TypeSyntaxCalibrated TV)
    (syntaxFit : ActualRawSyntax Va) (cover : ActualSelectedCoverOutput C) (covered : WindowSeedsCovered s) :
    ActualPackedWindow s (window C s
      (intrinsicQuery (selectedIntrinsic (windowUpdate base (refitTypeSyntax s T TV)))) Va) := by
  let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate base (refitTypeSyntax s T TV)))
  have w : ActualPackedWindow s baseW :=
    exact_OriginalRefitTypeSyntaxWindow s base T TV included baseFit original types
  exact exact_LiteralCoveredWindowCalibration C s (syntaxWindow baseW Va) cover covered
    (exact_SyntaxWindowCalibration s baseW Va w syntaxFit)

#print axioms exact_OriginalRefitTypeSyntaxGuard
#print axioms exact_OriginalRefitTypeSyntaxWindow
#print axioms exact_OriginalRefitTypeSyntaxCoveredWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRefitTypeSyntaxProof
