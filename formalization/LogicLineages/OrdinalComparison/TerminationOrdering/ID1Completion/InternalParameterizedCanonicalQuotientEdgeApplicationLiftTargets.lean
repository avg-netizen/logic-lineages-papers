module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalParameterizedCanonicalQuotientEdgeApplicationLift
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalParameterizedCanonicalApplicationCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ApplicationCalibrated n arity symbols S Gamma table data

/-- The actual original certificate fields and original lifted applications
are explicit witnesses. Their validity, tags, endpoint acceptance and both
representative equations must follow internally from W, N and actualJ. -/
def ActualParameterizedEncodedCanonicalQuotientEdgeApplicationLift : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (arrow d e x y a certificate out other s t k sourceApp targetApp liftedStep lifted parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((corePremises data oldStep arrow d e x y a certificate out other parameter ⊓
      constructorWitnesses d e a certificate s t k sourceApp targetApp liftedStep lifted).imp
      (edgeAccepted data oldStep out other lifted parameter)))

/-- Original Program totality eliminates all raw certificate/application
witnesses. The SAME checker, supplied actualJ outputs, RAW argument and
actual edgeLift output remain; no target typing or calibration is assumed. -/
def ActualParameterizedCanonicalQuotientEdgeApplicationLift : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (arrow d e x y a certificate out other lifted parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((liftPremises data oldStep arrow d e x y a certificate out other lifted parameter).imp
      (edgeAccepted data oldStep out other lifted parameter)))

/-- Both outputs are typed at the same codomain. Typing of y is derived by
the selected edge's propagation rule, without requiring an edgeLift witness. -/
def ActualParameterizedCanonicalQuotientEdgeApplicationTypedOutputs : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (arrow d e x y a certificate out other parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((corePremises data oldStep arrow d e x y a certificate out other parameter).imp
      (typedOutputs data e out other parameter)))

/-- Closed arrow construction and codomain membership are derived for the
same normalized Data at a symbolic pair(context,GammaCode). The source
antecedent has no fixed-Gamma fiber or extra target-typing hypothesis. -/
def ActualOriginalUniformNormalizedQuotientEdgeApplicationLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (baseData : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity baseData →
  ∀ oldStep : Program 4,
  InternalRuntimeLaw n (InternalOriginalUniformContextMembership.normalizeData baseData) oldStep

/-- One unchanged original base tuple and one oldStep precede every source
window, Gamma, internal body and symbolic input. Retain the previous normalized
canonical package, original quotient/application calibration and the proved
runtime application-lift law. This does not yet assert a path or outer-object
CertifiedApplicationLift, or the all-term accessibility endpoint. -/
def ActualOriginalUniformCanonicalQuotientEdgeApplicationSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ baseData : Data, ∃ oldStep : Program 4,
    InternalOriginalUniformDescentSelection.Calibrated n arity baseData ∧
    InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep ∧
    InternalOriginalUniformApplicationTyping.RetainedNormalizedPackage n arity baseData ∧
    SelectedCalibrated n arity
      (InternalOriginalUniformContextMembership.normalizeData baseData) oldStep ∧
    InternalRuntimeLaw n (InternalOriginalUniformContextMembership.normalizeData baseData) oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets
