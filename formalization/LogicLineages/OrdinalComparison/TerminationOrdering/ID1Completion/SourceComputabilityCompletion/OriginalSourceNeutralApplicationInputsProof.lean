module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationCoordinateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterGammaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPathVertexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterWindowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationInputsProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data validity)
open InternalApplicationStepPeel (graph5)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open OriginalSourceNeutralApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Original coordinate graphs are the internal Program-totality witnesses
in the public eliminator. The source domain pays shared Gamma and typing;
the original accepted application pays the output pair at the actual vertex. -/
theorem recoveredAt (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window)
    (oldComp : JointGammaComputability.Data) (oldVertex oldResult : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (functionObject argumentObject outputObject gammaCode function argument out parameter : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.left gammaCode functionObject)))
    (hf : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.right function functionObject)))
    (ha : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.right argument argumentObject)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing parameter
        (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) gammaCode)))
    (hd : Nonempty (Derivation body Gamma
      (InternalComputabilityDownward.domain
        (OuterSelection.computability oldComp base window oldVertex oldResult)
        (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau functionObject argumentObject)))
    (hjObject : Nonempty (Derivation body Gamma
      (InternalComputabilityApplication.accepted
        (OuterSelection.computability oldComp base window oldVertex oldResult) sigma tau
        (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table))
        functionObject argumentObject outputObject)))
    (hv : Nonempty (Derivation body Gamma
      (graph5 (Path.vertex (OuterSelection.data base window) window oldVertex) out parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument function))) :
    Nonempty (Derivation body Gamma
      (Recovered (OuterSelection.data base window) window
        (OuterSelection.computability oldComp base window oldVertex oldResult)
        (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau
        functionObject argumentObject outputObject gammaCode function argument out parameter)) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := OuterSelection.data base window
  have hwindow := OuterWindowProof.closedWindowEvaluation n window hw symbols S table hS
  have hwGraph := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Gamma) (α := alpha) window context hwindow
  have hgammaA := OuterGammaProof.argumentGamma oldComp data window oldVertex oldResult
    functionObject argumentObject gammaCode hg (andRight hd)
  have hfRaw := OuterCarrierSupportProof.typedRecover oldComp data window oldVertex oldResult
    context (numeral (typeNumber (.arrow sigma tau))) functionObject gammaCode function parameter
    hwGraph hg hf hp (andLeft (andLeft hd))
  have haRaw := OuterCarrierSupportProof.typedRecover oldComp data window oldVertex oldResult
    context (numeral (typeNumber sigma)) argumentObject gammaCode argument parameter
    hwGraph hgammaA ha hp (andRight (andLeft hd))
  have hj := OuterPathVertexProof.rawApplication n window hw symbols S table hS data oldVertex
    sigma tau parameter gammaCode function argument out hp hfRaw haRaw hv
  have hApp := OuterPathVertexProof.applicationPremises n arity base hc window hw symbols S table hS
    sigma tau parameter gammaCode function argument out hp hfRaw haRaw hj
  have hwindowRaw := OuterWindowProof.parameterWindow window context function parameter gammaCode hwGraph hp
  have hargFactors := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (validity data) data.member argument (numeral (typeNumber sigma)) parameter haRaw
  have hinput : Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.InputPremises data window
        (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
        (numeral (typeNumber tau)) function argument parameter)) :=
    andIntro hwindowRaw (andIntro (andLeft hApp)
      (andIntro (andLeft (andRight hApp)) (andIntro hfRaw
        (andIntro (andLeft (andRight hargFactors)) (andLeft (andRight (andRight hargFactors)))))))
  have hbranch := OuterResultSupportProof.resultBranchRecover oldComp data window oldVertex oldResult
    context sigma tau functionObject argumentObject outputObject hwindow hd hjObject
  have hout := OuterResultSupportProof.resultPair (Path.vertex data window oldVertex)
    context sigma tau functionObject argumentObject outputObject gammaCode function argument parameter out
    hg hf ha hp hv hbranch
  have hfunctionPair := reconstructPair functionObject gammaCode function hg hf
  have hargumentPair := reconstructPair argumentObject gammaCode argument hgammaA ha
  have hnonLambda := OriginalSourceNeutralApplicationCoordinateProof.nonLambdaIff functionObject function hf
  exact andIntro hd (andIntro hjObject (andIntro hfunctionPair (andIntro hargumentPair
    (andIntro hout (andIntro hp (andIntro hApp (andIntro hinput (andIntro hj hnonLambda))))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationInputsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationInputsProof
