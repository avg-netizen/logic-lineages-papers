module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterGammaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathRawProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof (reconstructPair)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open UniformCertificateCompletion

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The original source certificate preserves the shared runtime Gamma.
Its actual target payload and the paid source coordinates expose the SAME
positive path, retaining the original certificate witness and parameter. -/
theorem atTargetCoordinates (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) :
    let r := OriginalApplicationSidecar.finalInputs p
    let data := OuterSelection.data r.base r.window
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    ∀ (sigma tau : Ty)
      (F A X Y witness gammaCode function argument x y parameter : OTerm alpha),
    Nonempty (Derivation body Gamma
      (OriginalSourceNeutralApplication.Recovered data r.window
        (GlobalSourcePackage.computability r) context sigma tau
        F A X gammaCode function argument x parameter)) →
    Nonempty (Derivation body Gamma (OriginalSourceNeutralApplication.nonLambdaObject F)) →
    Nonempty (Derivation body Gamma
      (InternalAccessibilityRules.certificate (GlobalSourcePackage.source r)
        false context X Y witness)) →
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.right y Y)) →
    Nonempty (Derivation body Gamma
      (OriginalSourceNeutralApplicationPath.PathInputs data r.window r.oldStep
        (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r) context sigma tau
        F A X Y witness gammaCode function argument x y parameter)) := by
  dsimp only
  intro sigma tau F A X Y witness gammaCode function argument x y parameter hr hn hc hy
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hrCalibrated := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated
    n arity p hp
  have hwindow := OuterWindowProof.closedWindowEvaluation n r.window hrCalibrated.2.1
    symbols S table hS
  have hwGraph := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Gamma) (α := alpha) r.window context hwindow
  have hout := OriginalSourceNeutralApplicationFieldsProof.outputPairOf hr
  have hcoordinates := OuterResultSupportProof.outputCoordinates X gammaCode x hout
  have hg := andLeft hcoordinates
  have hx := andRight hcoordinates
  have hparameter := OriginalSourceNeutralApplicationFieldsProof.parameterPairOf hr
  have htargetGamma := OuterGammaProof.targetGamma r.oldSrc r.oldComp data
    (RawScalar.checker data) r.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    r.window context X Y witness gammaCode hg hc
  have htarget := reconstructPair Y gammaCode y htargetGamma hy
  have hrawGuarded := OuterPositiveRawProof.rawPositiveRecover r.oldSrc r.oldComp data
    (RawScalar.checker data) r.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    r.window context X Y witness gammaCode x y parameter hwGraph hg hx hy hparameter hc
  have hraw := OriginalVariableObjectSupportProof.positiveRecover data r.oldStep
    BottomRepresentative.bottomTest BottomSpineMeasure.measure x y witness parameter hrawGuarded
  have hnonLambda := OriginalSourceNeutralApplicationFieldsProof.nonLambdaOf hr hn
  exact andIntro hr (andIntro hn (andIntro hnonLambda (andIntro hc (andIntro htarget hraw))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathRawProof
