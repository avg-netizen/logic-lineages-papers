module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibility
open Source NumberedNumericCarrier PositiveArithmeticOperators PositiveArithmeticTransforms InternalCalculus
open UniformCertificateCompletion

/-- ALL original canonical scalar codes, with no caller-selected rank,
positive operator or calibration. The original relation and window are literal. -/
def CanonicalAccessibility (n : Nat) (arity : Fin n → Nat) : Prop :=
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → SourceEndpoint.strictTotalPrecedence table →
  ∀ (Gamma : List Ty) (value : Nat),
  canonicalCarrierTest n arity symbols S Gamma value = true →
  Acc (fun successor source => PositiveArithmeticOperators.encodedR n arity Gamma
    (OrdinaryArithmeticQuotient.contextCode symbols S table) source successor) value

/-- The SAME original relation on all well-formed encoded Objects, including
all ambient contexts and binder extensions in one relation. -/
def ObjectAccessibility (n : Nat) (arity : Fin n → Nat) : Prop :=
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → SourceEndpoint.strictTotalPrecedence table →
  ∀ (object : Nat),
  ContextUniform.encodedScalar n arity
    (OrdinaryArithmeticQuotient.contextCode symbols S table) object →
  Acc (fun successor source => ContextUniform.encodedR n arity
    (OrdinaryArithmeticQuotient.contextCode symbols S table) source successor) object

/-- Native membership in the standard least model of the ORIGINAL tagged
sourceBody, at src = source (finalInputs p). This is not an internal derivation. -/
def StandardLeastMembership (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → SourceEndpoint.strictTotalPrecedence table →
  ∀ (object : Nat),
  ContextUniform.encodedScalar n arity
    (OrdinaryArithmeticQuotient.contextCode symbols S table) object →
  standardLeastPredicate (SourcePresentation.sourceBody
    (GlobalSourcePackage.source (OriginalLambdaTraversalSelection.finalInputs p))
    (OrdinaryArithmeticQuotient.contextCode symbols S table)) (tagNumber false object)

/-- Truth of the ORIGINAL closed allTermsFormula in its standard least model.
No conditional closure/Acc hypothesis or alternate source Program is used. -/
def ClosedFormulaTruth (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → SourceEndpoint.strictTotalPrecedence table →
  let src := GlobalSourcePackage.source (OriginalLambdaTraversalSelection.finalInputs p)
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  realize (standardLeastPredicate (SourcePresentation.sourceBody src context))
    (SourcePresentation.allTermsFormula src context) Empty.elim

/-- ONE original tuple retains canonical cancellation/rank and ALL previous
properties, plus the explicit full Package at pF, before any window or Gamma.
D remains finalData p = OuterSelection.data pF.base pF.window. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  OriginalFinalObjectCoherence.Properties n arity p ∧
  GlobalSourcePackage.Package n arity
    (GlobalSourcePackage.source (OriginalLambdaTraversalSelection.finalInputs p))
    (GlobalSourcePackage.computability (OriginalLambdaTraversalSelection.finalInputs p))
    (GlobalSourcePackage.lift (OriginalLambdaTraversalSelection.finalInputs p)) ∧
  CanonicalAccessibility n arity ∧ ObjectAccessibility n arity ∧
  StandardLeastMembership n arity p ∧ ClosedFormulaTruth n arity p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibility
