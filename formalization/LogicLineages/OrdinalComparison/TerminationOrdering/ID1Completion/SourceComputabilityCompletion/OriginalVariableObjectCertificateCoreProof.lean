module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterGammaProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateCoreProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableObject OriginalVariableObjectSupportProof
open InternalComputabilityApplication InternalAccessibilityRules
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Open the original typed Object and original certificate at their SAME
runtime coordinates. Raw variable inversion determines the exact bottom
payload, and the original certificate supplies the target's shared Gamma.
All coordinate graphs are discharged by internal totality in the caller. -/
theorem certificateAtCoordinates (p : GlobalSourcePackage.Inputs) (context : Nat) (tau : Ty)
    (source target witness gammaCode x y parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 p.window (suc z) (numeral context))))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode source)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x source)))
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y target)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (ht : Nonempty (Derivation body Delta
      (typed (GlobalSourcePackage.computability (OriginalVariableRepresentative.refineInputs p))
        tau (numeral context) source)))
    (hv : Nonempty (Derivation body Delta (variableObject source)))
    (hc : Nonempty (Derivation body Delta
      (certificate (GlobalSourcePackage.source (OriginalVariableRepresentative.refineInputs p))
        false context source target witness))) :
    Nonempty (Derivation body Delta (bottomAtSourceGamma tau source target)) := by
  let r := OriginalVariableRepresentative.refineInputs p
  let data := OuterSelection.data r.base r.window
  let typ : OTerm α := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  have hrawTyped := OuterCarrierSupportProof.typedRecover r.oldComp data r.window
    r.oldVertex r.oldResult context typ source gammaCode x parameter hw hg hx hp ht
  have factors := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (InternalOriginalUniformDescentSelection.validity data) data.member
    x typ parameter hrawTyped
  have htype : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ x)) :=
    andLeft (andRight (andRight factors))
  have hvariable := variablePayloadRecover source x hv hx
  have hrawGuarded := OuterPositiveRawProof.rawPositiveRecover r.oldSrc r.oldComp data
    (RawScalar.checker data) r.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    r.window context source target witness gammaCode x y parameter hw hg hx hy hp hc
  have hraw := positiveRecover data r.oldStep BottomRepresentative.bottomTest
    BottomSpineMeasure.measure x y witness parameter hrawGuarded
  have hwindow := OuterWindowProof.parameterWindow p.window context x parameter gammaCode hw hp
  have hbottom := OriginalVariableQuotientPathProof.variablePositive p.base p.window p.oldStep
    x y witness parameter typ hwindow hvariable htype hraw
  have htargetGamma := OuterGammaProof.targetGamma r.oldSrc r.oldComp data
    (RawScalar.checker data) r.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    r.window context source target witness gammaCode hg hc
  exact bottomAtSourceGammaIntroduction tau source target gammaCode hg
    (bottomObjectAccept target gammaCode y typ htargetGamma hy hbottom)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateCoreProof
