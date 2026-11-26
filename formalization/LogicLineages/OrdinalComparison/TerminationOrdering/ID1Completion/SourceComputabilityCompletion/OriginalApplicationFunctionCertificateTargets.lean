module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedTypedFocus NumberedStepCertificate NumberedNumericStep
open OriginalApplicationFunctionCertificateDefinitions
/-- Exact native typed checker equality, including rejection, for the same
argument and SAME runtime context. Not an internal oldStep introduction. -/
def ActualTypedLift : Prop :=
 ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
 (table : Fin n → Fin n → Bool) (sigma tau : Ty)
 (fn fnOut : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
 (arg : AuxTerm (Fin n) arity Gamma sigma) (child : StepCertificate),
 stepTest n arity symbols S Gamma table (.app fn arg) (.app fnOut arg) (liftCertificate child) =
 stepTest n arity symbols S Gamma table fn fnOut child
/-- Literal original encoding: arbitrary numbers preserve the replacement/root
pair, and prefix/strip are exact on encoded certificates. -/
def ActualCoding : Prop :=
 (∀ raw : Nat, (Nat.unpair (stripStep raw)).2 = (Nat.unpair raw).2) ∧
 (∀ raw : Nat, stripStep (liftStep raw) = raw) ∧
 (∀ child : StepCertificate, liftStep (stepCertificateNumber child) = stepCertificateNumber (liftCertificate child)) ∧
 (∀ child : StepCertificate, stripStep (stepCertificateNumber (liftCertificate child)) = stepCertificateNumber child)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateTargets
