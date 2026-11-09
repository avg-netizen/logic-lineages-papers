module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalOriginalUniformStepGuard
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Arbitrary actual binary validity and four-input core ASTs. The source
tag alone is given; original totality must expose and recover the target tag.
No semantic calibration, decoding or assumed type-preservation rule occurs. -/
def ActualParameterizedGuardedStepAtSourceTag : Prop :=
  ∀ (body : Positive (Fin 1)) (sourceValid targetValid : Program 2) (core : Program 4)
    (α : Type) (Delta : List (Formula α))
    (tag s t k parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph1 InternalUnpair.left tag s).imp
      ((guardedAccepted sourceValid targetValid core s t k parameter).iff
        (taggedRequirements sourceValid targetValid core tag s t k parameter))))

/-- Exact source/target/type/core factorization for the literal selected W.
The source tag is symbolic, target-source validity is recovered from W, and
the same original parameter appears in every binary and four-input call. -/
def ActualParameterizedCanonicalStepAtSourceTag : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (tag s t k parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph1 InternalUnpair.left tag s).imp
      ((stepAccepted data oldStep s t k parameter).iff
        (stepRequirements data oldStep tag s t k parameter))))

/-- The original source-universe/packed-target/type wrapper retains the
entire original numeric step function for every window and Gamma. Both leaf
calibrations are global and all raw triples remain included. -/
def ActualOriginalUniformGuardedStepCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  GuardedCalibrated n arity data oldStep

/-- At a subtype-closed window, original accepted steps preserve source
validity, so the extra raw-target SOURCE-validity conjunct is redundant.
This is an equality on every raw input, with no acceptance/decode hypothesis. -/
def ActualOriginalUniformCanonicalStepCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  SelectedCalibrated n arity data oldStep

/-- The SAME selected W accepts the original lifted raw applications and
stepLift output. Endpoint factors and W's V(raw target) must derive the new
guards internally through actual validator closure. No semantic calibration,
subtype closure, result-fold success or application-lift theorem is assumed. -/
def ActualParameterizedCanonicalStepApplication : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (arrow d e s t a k sourceApp targetApp liftedStep parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((liftPremises data arrow d e s t a k sourceApp targetApp liftedStep parameter ⊓
      stepAccepted data oldStep s t k parameter).imp
      (stepAccepted data oldStep sourceApp targetApp liftedStep parameter)))

/-- For each globally calibrated unchanged Data, ONE original oldStep AST
precedes every window, Gamma, internal body, context and symbolic parameter.
Both literal constructed wrappers retain all-input original calibration and
the same W has the internal factorization/application laws. -/
def ActualOriginalUniformCanonicalStepSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∃ oldStep : Program 4,
    InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep ∧
      (GuardedCalibrated n arity data oldStep ∧
        (SelectedCalibrated n arity data oldStep ∧ InternalLaws data oldStep))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardTargets
