module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDomainCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPathVertexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterRawPreparationProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationStepPeel (graph5)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open SourceComputabilityCompletion
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Prepare BOTH original application blocks and raw codomain typings
from the original source domain/certificate at actual queried coordinates.
Target typing, codomain membership and vertex activation are derived.
The coordinate hypotheses are internal totality witnesses in the full lift,
not new conditions on its unchanged unqualified statement. -/
theorem prepare (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window)
    (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (oldStep : Program 4) (oldVertex oldResult : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (f g a witness gammaCode x y argument parameter out other : OTerm α)
    (hwindow : evaluate window (List.Vector.ofFn ![OrdinaryArithmeticQuotient.contextCode symbols S table]) = 1)
    (hgamma : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y g)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument a)))
    (hp : Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.parameterGraph
        (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode)))
    (hd : Nonempty (Derivation body Delta
      (domain (OuterSelection.computability oldComp base window oldVertex oldResult)
        (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau f a)))
    (hcert : Nonempty (Derivation body Delta
      (certificate (OuterSelection.source oldSrc oldComp base oldStep window) false
        (OrdinaryArithmeticQuotient.contextCode symbols S table) f g witness)))
    (hvertexF : Nonempty (Derivation body Delta
      (graph5 (Path.vertex (OuterSelection.data base window) window oldVertex) out parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x)))
    (hvertexG : Nonempty (Derivation body Delta
      (graph5 (Path.vertex (OuterSelection.data base window) window oldVertex) other parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument y))) :
    let data := OuterSelection.data base window
    let arrow := numeral (typeNumber (.arrow sigma tau))
    let d := numeral (typeNumber sigma)
    let e := numeral (typeNumber tau)
    Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.applicationPremises data arrow d e x argument out parameter ⊓
        (InternalOriginalUniformApplicationTyping.applicationPremises data arrow d e y argument other parameter ⊓
          (typedAccepted data out e parameter ⊓
            (typedAccepted data other e parameter ⊓
              graph4 (Outer.rawPositive data oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure)
                (suc z) x y witness parameter))))) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := OuterSelection.data base window
  have hwGraph := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Delta) (α := α) window context hwindow
  have hgammaA := OuterGammaProof.argumentGamma oldComp data window oldVertex oldResult
    f a gammaCode hgamma (andRight hd)
  have hgammaG := OuterGammaProof.targetGamma oldSrc oldComp data (RawScalar.checker data)
    oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure window context f g witness gammaCode hgamma hcert
  have htypedG := OuterDomainCertificateProof.targetTyped oldSrc oldComp data (RawScalar.checker data)
    oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure window oldVertex oldResult
    context (.arrow sigma tau) f g witness hwindow (andLeft (andLeft hd)) hcert
  have hfRaw := OuterCarrierSupportProof.typedRecover oldComp data window oldVertex oldResult
    context (numeral (typeNumber (.arrow sigma tau))) f gammaCode x parameter
    hwGraph hgamma hx hp (andLeft (andLeft hd))
  have hgRaw := OuterCarrierSupportProof.typedRecover oldComp data window oldVertex oldResult
    context (numeral (typeNumber (.arrow sigma tau))) g gammaCode y parameter
    hwGraph hgammaG hy hp htypedG
  have haRaw := OuterCarrierSupportProof.typedRecover oldComp data window oldVertex oldResult
    context (numeral (typeNumber sigma)) a gammaCode argument parameter
    hwGraph hgammaA ha hp (andRight (andLeft hd))
  have hjF := OuterPathVertexProof.rawApplication n window hw symbols S table hS data oldVertex
    sigma tau parameter gammaCode x argument out hp hfRaw haRaw hvertexF
  have hjG := OuterPathVertexProof.rawApplication n window hw symbols S table hS data oldVertex
    sigma tau parameter gammaCode y argument other hp hgRaw haRaw hvertexG
  have hAppF := OuterPathVertexProof.applicationPremises n arity base hc window hw symbols S table hS
    sigma tau parameter gammaCode x argument out hp hfRaw haRaw hjF
  have hAppG := OuterPathVertexProof.applicationPremises n arity base hc window hw symbols S table hS
    sigma tau parameter gammaCode y argument other hp hgRaw haRaw hjG
  have htypeF := InternalOriginalUniformApplicationTypingApplicationProof.applicationTyped data
    (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    x argument out parameter hAppF
  have htypeG := InternalOriginalUniformApplicationTypingApplicationProof.applicationTyped data
    (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    y argument other parameter hAppG
  have hraw := OuterPositiveRawProof.rawPositiveRecover oldSrc oldComp data (RawScalar.checker data)
    oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure window context
    f g witness gammaCode x y parameter hwGraph hgamma hx hy hp hcert
  exact andIntro hAppF (andIntro hAppG (andIntro htypeF (andIntro htypeG hraw)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterRawPreparationProof
