module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLift
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

/-- The SAME selected finite leaves, with no additional correctness, closure,
representative-congruence, typing-invariant or lifting field. -/
abbrev Data := InternalCertifiedSourceGuardSelection.Data

/-- The original quotient-edge core on the exact selected step and the two
distinct tagged representatives. This is NOT the outer typed-edge wrapper. -/
def coreAccepted {α : Type} (data : Data) (x y certificate : OTerm α) : Formula α :=
  InternalQuotientEdgeChecker.accepted
    (InternalCertifiedSourceGuardSelection.edgeData data) x y certificate

/-- Only the original endpoint/application/step-lift graphs, selected child
step acceptance and the actual argument good-run graph. Parent source
validity and both parent good runs are conclusions to be derived. -/
def stepLiftPremises {α : Type} (data : Data)
    (arrow d e s t a k sourceApp targetApp liftedStep : OTerm α) : Formula α :=
  InternalOriginalApplicationStep.liftPremises
      (InternalCertifiedSourceGuardSelection.baseData data)
      arrow d e s t a k sourceApp targetApp liftedStep ⊓
    (InternalCertifiedSourceGuardSelection.stepAccepted data s t k ⊓
      graph1 (InternalCertifiedSourceGuardSelection.goodRun data)
        InternalOriginalStepGuard.one a)

/-- Actual selected canonical source/argument acceptance, original core-edge
acceptance, and the two exact combine graphs at the SAME argument. Types are
the original closed type codes. In particular y is not assumed typed. -/
def corePremises {α : Type} (data : Data) (sigma tau : Ty)
    (x y a certificate out other : OTerm α) : Formula α :=
  InternalCertifiedSourceGuardSelection.typedAccepted data x
      (numeral (typeNumber (.arrow sigma tau))) ⊓
    (InternalCertifiedSourceGuardSelection.typedAccepted data a
        (numeral (typeNumber sigma)) ⊓
      (coreAccepted data x y certificate ⊓
        (graph4 (InternalRepresentativeFoldCalibration.combine data.oldEdge) out
            (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x a ⊓
          graph4 (InternalRepresentativeFoldCalibration.combine data.oldEdge) other
            (numeral (typeNumber sigma)) (numeral (typeNumber tau)) y a)))

/-- Opened witnesses use only the ORIGINAL edge/application/step constructors.
The shared raw fields are constrained by actual Program graphs, including
certificate zero and malformed codes; no alternate certificate is chosen. -/
def constructorWitnesses {α : Type} (sigma tau : Ty)
    (a certificate s t k sourceApp targetApp liftedStep lifted : OTerm α) : Formula α :=
  InternalApplicationCertificateConstructors.liftPremises
      (numeral (typeNumber sigma)) (numeral (typeNumber tau))
      a certificate s t k sourceApp targetApp liftedStep ⊓
    graph3 edgeCode lifted sourceApp targetApp liftedStep

/-- The witness-free local interface. edgeLift has arity FOUR and receives
[domain,codomain,argument,certificate], in that unchanged order. -/
def liftPremises {α : Type} (data : Data) (sigma tau : Ty)
    (x y a certificate out other lifted : OTerm α) : Formula α :=
  corePremises data sigma tau x y a certificate out other ⊓
    graph4 edgeLift lifted (numeral (typeNumber sigma)) (numeral (typeNumber tau))
      a certificate

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLift
