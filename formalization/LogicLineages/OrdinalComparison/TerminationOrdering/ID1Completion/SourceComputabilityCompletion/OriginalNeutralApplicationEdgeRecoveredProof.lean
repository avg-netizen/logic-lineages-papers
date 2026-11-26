module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeRecoveredProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion OriginalNeutralApplicationEdge
open OriginalNeutralApplicationEdgeTransportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Component functionality identifies the actual child edge with the
requested function. Its original typed propagation supplies the target's
typed input, and the actualJ equation rebuilds the target at the unchanged
requested raw argument. The complete generic recovered trace is retained. -/
theorem recoveredAt (p : GlobalSourcePackage.Inputs) :
    let r := OriginalApplicationSidecar.finalInputs p
    let data := OuterSelection.data r.base r.window
    ∀ arrow d e function argument x y certificate parameter
      S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child F G A argumentOut : OTerm alpha,
    Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.InputPremises data r.window arrow d e function argument parameter)) →
    Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.Recovered data d e function argument x argumentOut parameter)) →
    Nonempty (Derivation body Gamma
      (OriginalNeutralQuotient.Recovered data r.oldStep x y certificate parameter
        S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child F G A)) →
    Nonempty (Derivation body Gamma
      (Recovered data r.oldStep arrow d e function argument x y certificate parameter
        S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child F G A argumentOut)) := by
  dsimp only
  intro arrow d e function argument x y certificate parameter
    S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child F G A argumentOut
    hi hrequested hquotient
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  have heqs := OriginalNeutralApplicationEdgeFieldsProof.componentEqualities data r.window r.oldStep
    arrow d e function argument x y certificate parameter
    S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child F G A argumentOut
    hi hrequested hquotient
  have hd := andLeft heqs
  have he := andLeft (andRight heqs)
  have hf := andLeft (andRight (andRight heqs))
  have ha := andRight (andRight (andRight heqs))
  have hchild := andLeft (andRight (andRight (andRight (andRight hquotient))))
  have hedgeRaw := andRight (andRight (andRight (andRight (andRight (andRight hchild)))))
  have hedge : Nonempty (Derivation body Gamma
      (edgeAccepted data r.oldStep function G child parameter)) :=
    fourInputs (edgeChecker data r.oldStep) (suc z) F G child parameter
      function G child parameter hf (equalSelf G) (equalSelf child)
      (equalSelf parameter) hedgeRaw
  have hft := andLeft (andRight (andRight (andRight hi)))
  have hgt := TypingProof.typedPropagation data r.oldStep function G child arrow parameter hft hedge
  have htail := andRight (andRight (andRight (andRight (andRight hquotient))))
  have htargetRaw := andRight (andRight htail)
  have htarget : Nonempty (Derivation body Gamma (graph4 application y d e G argumentOut)) :=
    fourInputs application y rawD rawE G A d e G argumentOut
      hd he (equalSelf G) ha htargetRaw
  have hw := BottomDescentStepProof.windowChange r.window (suc z) function G parameter (andLeft hi)
  have hinput : Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.InputPremises data r.window arrow d e G argument parameter)) :=
    andIntro hw (andIntro (andLeft (andRight hi))
      (andIntro (andLeft (andRight (andRight hi)))
        (andIntro hgt (andRight (andRight (andRight (andRight hi)))))))
  have hj := OriginalNeutralApplicationEdgeBridgeProof.finalBackward p
    arrow d e G argument y argumentOut parameter hinput (andLeft hrequested) htarget
  exact andIntro hquotient (andIntro hrequested (andIntro hd (andIntro he
    (andIntro hf (andIntro ha (andIntro hedge (andIntro hgt hj)))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeRecoveredProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeRecoveredProof
