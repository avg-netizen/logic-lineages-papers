module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterRawPreparationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterRawLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterLiftSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCertificateCoordinatesProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open SourceComputabilityCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- At original totality witnesses, recover both supplied output Objects
through the actual result builder, lift the original supplied certificate,
and reassemble every literal outer guard. No output coordinate or typing
condition will remain in the unqualified endpoint. -/
theorem atCoordinates (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window)
    (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (oldStep : Program 4) (oldVertex oldResult : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (f g a out other witness lifted gammaCode x y argument parameter rawOut rawOther : OTerm α)
    (hgamma : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y g)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument a)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter
        (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) gammaCode)))
    (hvF : Nonempty (Derivation body Delta
      (graph5 (Path.vertex (OuterSelection.data base window) window oldVertex) rawOut parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x)))
    (hvG : Nonempty (Derivation body Delta
      (graph5 (Path.vertex (OuterSelection.data base window) window oldVertex) rawOther parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument y)))
    (hd : Nonempty (Derivation body Delta
      (domain (OuterSelection.computability oldComp base window oldVertex oldResult)
        (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau f a)))
    (hcert : Nonempty (Derivation body Delta
      (certificate (OuterSelection.source oldSrc oldComp base oldStep window) false
        (OrdinaryArithmeticQuotient.contextCode symbols S table) f g witness)))
    (hacceptedF : Nonempty (Derivation body Delta
      (accepted (OuterSelection.computability oldComp base window oldVertex oldResult) sigma tau
        (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) f a out)))
    (hacceptedG : Nonempty (Derivation body Delta
      (accepted (OuterSelection.computability oldComp base window oldVertex oldResult) sigma tau
        (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) g a other)))
    (hlift : Nonempty (Derivation body Delta
      (programGraph (OuterSelection.lift base window oldVertex) lifted
        (liftArguments (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau a witness)))) :
    Nonempty (Derivation body Delta
      (certificate (OuterSelection.source oldSrc oldComp base oldStep window) false
        (OrdinaryArithmeticQuotient.contextCode symbols S table) out other lifted)) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := OuterSelection.data base window
  have hwindow := OuterWindowProof.closedWindowEvaluation n window hw symbols S table hS
  have hwGraph := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Delta) (α := α) window context hwindow
  have hgammaA := OuterGammaProof.argumentGamma oldComp data window oldVertex oldResult
    f a gammaCode hgamma (andRight hd)
  have hgammaG := OuterGammaProof.targetGamma oldSrc oldComp data (RawScalar.checker data)
    oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure window context
    f g witness gammaCode hgamma hcert
  have hdG := OuterDomainCertificateProof.targetDomain oldSrc oldComp data (RawScalar.checker data)
    oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure window oldVertex oldResult
    context sigma tau f g a witness gammaCode hwindow hgamma hd hcert
  have hresultF := OuterResultSupportProof.resultBranchRecover oldComp data window oldVertex oldResult
    context sigma tau f a out hwindow hd hacceptedF
  have hresultG := OuterResultSupportProof.resultBranchRecover oldComp data window oldVertex oldResult
    context sigma tau g a other hwindow hdG hacceptedG
  have hpairF := OuterResultSupportProof.resultPair (Path.vertex data window oldVertex)
    context sigma tau f a out gammaCode x argument parameter rawOut hgamma hx ha hp hvF hresultF
  have hpairG := OuterResultSupportProof.resultPair (Path.vertex data window oldVertex)
    context sigma tau g a other gammaCode y argument parameter rawOther hgammaG hy ha hp hvG hresultG
  have hcoordsF := OuterResultSupportProof.outputCoordinates out gammaCode rawOut hpairF
  have hcoordsG := OuterResultSupportProof.outputCoordinates other gammaCode rawOther hpairG
  have prepared := OuterRawPreparationProof.prepare n arity base hc window hw
    oldSrc oldComp oldStep oldVertex oldResult symbols S table hS sigma tau
    f g a witness gammaCode x y argument parameter rawOut rawOther hwindow
    hgamma hx hy ha hp hd hcert hvF hvG
  have happF := andLeft prepared
  have happG := andLeft (andRight prepared)
  have htypedF := andLeft (andRight (andRight prepared))
  have htypedG := andLeft (andRight (andRight (andRight prepared)))
  have hraw := andRight (andRight (andRight (andRight prepared)))
  have hm := OuterLiftSupportProof.mappedRecover data window oldVertex context sigma tau
    a witness lifted gammaCode argument parameter hgammaA ha hp hlift
  have liftedRaw := OuterRawLiftProof.rawLift n arity base hc window hw oldStep oldVertex
    symbols S table hS sigma tau parameter gammaCode x y argument witness rawOut rawOther lifted
    hp happF happG hraw hvF hvG hm
  exact OuterPositiveProof.positiveAccept oldSrc oldComp data (RawScalar.checker data) oldStep
    BottomRepresentative.bottomTest BottomSpineMeasure.measure window context
    (numeral (typeNumber tau)) out other lifted gammaCode rawOut rawOther parameter hwGraph
    (andLeft hcoordsF) (andLeft hcoordsG) (andRight hcoordsF) (andRight hcoordsG)
    hp htypedF htypedG liftedRaw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCertificateCoordinatesProof
