module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityCanonicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativePreparationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaSemanticsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityStandardProof
open Source PositiveArithmeticOperators PositiveArithmeticTransforms InternalCalculus
open UniformCertificateCompletion OriginalFinalNativeAccessibility
open OriginalFinalNativeAccessibilityCanonicalProof

/-- Retain the literal complete original Package at pF, rather than at the
old p. The same construction supplies source calibration for the model proof. -/
theorem finalPackage (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.Package n arity
      (GlobalSourcePackage.source (OriginalLambdaTraversalSelection.finalInputs p))
      (GlobalSourcePackage.computability (OriginalLambdaTraversalSelection.finalInputs p))
      (GlobalSourcePackage.lift (OriginalLambdaTraversalSelection.finalInputs p)) := by
  have hpF :=
    (OriginalLambdaTraversalNativePreparationProof.actualOriginalLambdaTraversalNativePreparation
      n arity p hp).2.1
  exact (GlobalSourcePackageProof.actualOriginalGlobalSourcePackageConstruction
    n arity (OriginalLambdaTraversalSelection.finalInputs p) hpF).2.2

/-- A supporting native induction, not arithmetic reflection. The induction
motive retains the exact scalar carrier so every successor can enter the SAME
original tagged sourceBody. -/
theorem accessibleStandardLeast (data : SourcePresentation.Data)
    (n : Nat) (arity : Fin n → Nat) (hcal : ContextUniform.Calibrated data n arity)
    (context : Nat) (hclosed : SourceArithmeticAccessibility.DecodedSubtypeClosed n context)
    (object : Nat) (hobject : ContextUniform.encodedScalar n arity context object)
    (ha : Acc (fun successor source => ContextUniform.encodedR n arity context source successor) object) :
    standardLeastPredicate (SourcePresentation.sourceBody data context) (tagNumber false object) := by
  induction ha with
  | intro object hacc ih =>
    apply (InternalCalculusSupportProof.standardUnfolding
      (SourcePresentation.sourceBody data context) (tagNumber false object)).mpr
    have hv : (fun _ : Fin 1 => tagNumber false object) = ![tagNumber false object] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]
    apply (JointGammaSemanticsProof.actualClosedSourceOperator data n arity hcal context
      (standardLeastPredicate (SourcePresentation.sourceBody data context)) object).1.mpr
    refine ⟨hobject,?_⟩
    intro y hy
    exact ih y hy (objectScalarPreservation n arity context hclosed object y hobject hy)

/-- ALL original encoded scalar Objects enter the exact standard least model
of the SAME final source. No caller-supplied accessibility remains. -/
theorem actualOriginalFinalStandardLeastMembership :
    OriginalFinalNativeAccessibilityTargets.ActualOriginalFinalStandardLeastMembership := by
  intro n arity p hp symbols S table hclosed htable object hobject
  exact accessibleStandardLeast
    (GlobalSourcePackage.source (OriginalLambdaTraversalSelection.finalInputs p))
    n arity (finalPackage n arity p hp).1
    (OrdinaryArithmeticQuotient.contextCode symbols S table)
    ⟨((symbols,S),table),by simp [OrdinaryArithmeticQuotient.contextCode],hclosed⟩
    object hobject
    (actualOriginalContextObjectAccessibility n arity symbols S table hclosed htable object hobject)

/-- Discharge the original arbitrary-P equivalence at its standard least
predicate, producing actual truth of the original CLOSED formula. -/
theorem actualOriginalFinalClosedFormulaTruth :
    OriginalFinalNativeAccessibilityTargets.ActualOriginalFinalClosedFormulaTruth := by
  intro n arity p hp symbols S table hclosed htable
  apply (JointGammaSemanticsProof.actualAllTermsFormulaTruth
    (GlobalSourcePackage.source (OriginalLambdaTraversalSelection.finalInputs p))
    n arity (finalPackage n arity p hp).1
    (OrdinaryArithmeticQuotient.contextCode symbols S table) _).mpr
  exact actualOriginalFinalStandardLeastMembership n arity p hp symbols S table hclosed htable

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityStandardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityStandardProof
