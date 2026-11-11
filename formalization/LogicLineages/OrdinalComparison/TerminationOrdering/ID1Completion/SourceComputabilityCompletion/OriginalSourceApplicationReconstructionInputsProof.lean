module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionResultProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionInputsProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open UniformCertificateCompletion OriginalSourceApplicationReconstruction
open OriginalSourceNeutralApplicationFieldsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- At internally supplied pair witnesses, derive the full original Object
domain, accepted application and output typing from the paid raw graphs. -/
theorem recoveredAt (oldComp : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (sigma tau : Ty)
    (F A X gammaCode function argument out parameter targetFunction vertex G V : OTerm alpha)
    (hinput : Nonempty (Derivation body Gamma
      (OriginalSourceNeutralApplication.Recovered data window
        (Outer.computability oldComp data window oldVertex oldResult) context sigma tau
        F A X gammaCode function argument out parameter)))
    (hfunction : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.typedGraph data targetFunction
        (numeral (typeNumber (.arrow sigma tau))) parameter)))
    (hj : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph data vertex
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) targetFunction argument parameter)))
    (hG : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing G gammaCode targetFunction)))
    (hV : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing V gammaCode vertex))) :
    Nonempty (Derivation body Gamma
      (Recovered data window (Outer.computability oldComp data window oldVertex oldResult)
        context sigma tau F A X gammaCode function argument out parameter targetFunction vertex G V)) := by
  let comp := Outer.computability oldComp data window oldVertex oldResult
  let arrow : OTerm alpha := numeral (typeNumber (.arrow sigma tau))
  let d : OTerm alpha := numeral (typeNumber sigma)
  let e : OTerm alpha := numeral (typeNumber tau)
  have hp := parameterPairOf hinput
  have hA := argumentPairOf hinput
  have hd := domainOf hinput
  have hneutral := inputPremisesOf hinput
  have hwindow := OriginalSourceApplicationReconstructionWindowProof.windowAtContext
    window context function parameter gammaCode (andLeft hneutral) hp
  have happ := applicationPremisesOf hinput
  have har := andLeft happ
  have hm := andLeft (andRight happ)
  have hargument := andLeft (andRight (andRight (andRight happ)))
  have hGleft := pairLeft G gammaCode targetFunction hG
  have hGright := pairRight G gammaCode targetFunction hG
  have hAleft := pairLeft A gammaCode argument hA
  have hAright := pairRight A gammaCode argument hA
  have hGtyped := OuterTypedProof.typedAccept oldComp data window oldVertex oldResult
    context arrow G gammaCode targetFunction parameter hwindow hGleft hGright hp hfunction
  have hguard := OuterTypedProof.objectGuard oldComp data window oldVertex oldResult
    G A gammaCode hGleft hAleft
  have hdomain : Nonempty (Derivation body Gamma
      (InternalComputabilityDownward.domain comp context sigma tau G A)) :=
    andIntro (andIntro hGtyped (andRight (andLeft hd))) hguard
  have hactive := OriginalSourceApplicationReconstructionWindowProof.rawActivation data window context
    arrow d e targetFunction argument parameter gammaCode hwindow hp har hfunction hargument
  have hvertex := PathSupportProof.vertexAccept data window oldVertex
    (Path.arguments parameter d e argument targetFunction) vertex hactive hj
  have hbranch := OriginalSourceApplicationReconstructionBranchProof.resultBranchValue
    (Path.vertex data window oldVertex) context sigma tau G A V gammaCode
    targetFunction argument parameter vertex hGleft hGright hAright hp hvertex hV
  have haccepted := OriginalSourceApplicationReconstructionResultProof.acceptedAt
    oldComp data window oldVertex oldResult context sigma tau G A V hwindow har hdomain hbranch
  have htarget : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises data
        arrow d e targetFunction argument vertex parameter)) :=
    andIntro har (andIntro hm (andIntro hfunction (andIntro hargument hj)))
  have hrawTyped := InternalOriginalUniformApplicationTypingApplicationProof.applicationTyped
    data arrow d e targetFunction argument vertex parameter htarget
  have hVtyped := OuterTypedProof.typedAccept oldComp data window oldVertex oldResult
    context e V gammaCode vertex parameter hwindow
    (pairLeft V gammaCode vertex hV) (pairRight V gammaCode vertex hV) hp hrawTyped
  exact andIntro hinput (andIntro hfunction (andIntro hj (andIntro hG (andIntro hV
    (andIntro hGtyped (andIntro hdomain (andIntro haccepted hVtyped)))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionInputsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionInputsProof
