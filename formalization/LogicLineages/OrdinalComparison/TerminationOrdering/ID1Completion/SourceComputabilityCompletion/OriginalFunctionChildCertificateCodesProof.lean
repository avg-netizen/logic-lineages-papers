module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateCodesProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open UniformCertificateCompletion OriginalSourceNeutralApplicationFieldsProof
open OriginalFunctionChildCertificate
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Reinsert the literal raw positive checker and every original Object
activation, typing and SAME-Gamma guard at the already reconstructed Objects. -/
theorem atCodes (p : GlobalSourcePackage.Inputs) :
    let q := OriginalSpineGuardLeaf.refineInputs p
    let r := OriginalApplicationSidecar.finalInputs q
    let data := OuterSelection.data r.base r.window
    ∀ (context : Nat) (sigma tau : Ty)
      (F A X gammaCode function argument out parameter targetFunction vertex G V child entry pathCode : OTerm alpha),
    Nonempty (Derivation body Gamma
      (OriginalSourceApplicationReconstruction.Recovered data r.window
        (GlobalSourcePackage.computability r) context sigma tau
        F A X gammaCode function argument out parameter targetFunction vertex G V)) →
    Nonempty (Derivation body Gamma (edgeAccepted data r.oldStep function targetFunction child parameter)) →
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing entry targetFunction child)) →
    Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode pathCode entry z)) →
    Nonempty (Derivation body Gamma
      (Recovered data r.window r.oldStep (GlobalSourcePackage.source r)
        (GlobalSourcePackage.computability r) context sigma tau
        F A X gammaCode function argument out parameter targetFunction vertex G V child entry pathCode)) := by
  dsimp only
  intro context sigma tau F A X gammaCode function argument out parameter targetFunction vertex G V child entry pathCode
    hrec he hentry hpath
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  let data := OuterSelection.data r.base r.window
  have hinput := andLeft hrec
  have htargetTyped := andLeft (andRight hrec)
  have hG := andLeft (andRight (andRight (andRight hrec)))
  have hF := functionPairOf hinput
  have hp := parameterPairOf hinput
  have hw := andLeft (inputPremisesOf hinput)
  have hcontext := OriginalSourceApplicationReconstructionWindowProof.windowAtContext
    r.window context function parameter gammaCode hw hp
  have happ := applicationPremisesOf hinput
  have hsourceTyped := andLeft (andRight (andRight happ))
  obtain ⟨hquotientLaw⟩ := OriginalQuotientSpineProof.actualOriginalFinalQuotientSpineGuard p
    body alpha Gamma function targetFunction child parameter
  obtain ⟨hquotientInput⟩ := andIntro hw he
  have hguard : Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted function targetFunction child parameter)) :=
    ⟨Derivation.implicationElimination hquotientLaw hquotientInput⟩
  have hpositive := OriginalFunctionChildCertificateGuardProof.singletonPositive data r.oldStep
    function targetFunction child entry pathCode parameter he hentry hpath
  have hraw := OriginalFunctionChildCertificateGuardProof.positiveFromGuard
    (edgeChecker data r.oldStep) function targetFunction child pathCode parameter hguard hpositive
  have hcertificate := OuterPositiveProof.positiveAccept r.oldSrc r.oldComp data
    (RawScalar.checker data) r.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure r.window
    context (numeral (typeNumber (.arrow sigma tau))) F G pathCode gammaCode function targetFunction parameter
    hcontext (pairLeft F gammaCode function hF) (pairLeft G gammaCode targetFunction hG)
    (pairRight F gammaCode function hF) (pairRight G gammaCode targetFunction hG)
    hp hsourceTyped htargetTyped hraw
  exact andIntro hrec (andIntro he (andIntro hentry (andIntro hpath hcertificate)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateCodesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateCodesProof
