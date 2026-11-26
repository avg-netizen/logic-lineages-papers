module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientRecoveredProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion UniformCertificateCompletion.SupportProof
open ClaudeSupervisedCompletion OriginalNeutralQuotient OriginalNeutralQuotientSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The accepted original raw step provides both parent validities. Its
peeled record provides the literal arrow and child type graphs. The SAME
argument fold then rebuilds both canonical application endpoints. -/
theorem atChildren (p : GlobalSourcePackage.Inputs) :
    let r := OriginalApplicationSidecar.finalInputs p
    let data := OuterSelection.data r.base r.window
    ∀ x y certificate parameter S T K state d e arrow f g a k child F G A : OTerm alpha,
    Nonempty (Derivation body Gamma (selectors certificate S T K)) →
    Nonempty (Derivation body Gamma (requirements data r.oldStep x y S T K parameter)) →
    Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph r.window x parameter)) →
    Nonempty (Derivation body Gamma (graph3 edgeCode state S T K)) →
    Nonempty (Derivation body Gamma
      (InverseGuardTargets.Peeled (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
        r.oldStep d e arrow f g a k child InternalOriginalStepGuard.one state S T K parameter)) →
    Nonempty (Derivation body Gamma
      (OriginalUniformStepQuotientTargets.Recovered data r.oldStep f g k F G child parameter)) →
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph data A a parameter)) →
    Nonempty (Derivation body Gamma
      (Recovered data r.oldStep x y certificate parameter S T K state d e arrow f g a k child F G A)) := by
  dsimp only
  intro x y certificate parameter S T K state d e arrow f g a k child F G A
    hselectors hrequirements hw hstate hpeeled hchild ha
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  have hconstructors := andLeft (andLeft (andRight hpeeled))
  have har := andLeft hconstructors
  have hfType := andLeft (andRight hconstructors)
  have hgType := andLeft (andRight (andRight hconstructors))
  have haType := andLeft (andRight (andRight (andRight hconstructors)))
  have htail := andRight (andRight (andRight (andRight hconstructors)))
  have hsapp := andLeft (andRight htail)
  have htapp := andLeft (andRight (andRight htail))
  obtain ⟨hvs,hvt,_⟩ := TypingProof.stepParts data r.oldStep S T K parameter (andLeft hrequirements)
  have hns := TypingProof.sourceFold data x S parameter hvs (andLeft (andRight hrequirements))
  have hnt := andRight (andRight hrequirements)
  have hnf := andLeft (andRight (andRight (andRight hchild)))
  have hng := andLeft (andRight (andRight (andRight (andRight hchild))))
  have hws := BottomDescentStepProof.windowChange r.window (suc z) x S parameter hw
  have hwt := BottomDescentStepProof.windowChange r.window (suc z) x T parameter hw
  have hx := OriginalNeutralQuotientApplicationProof.finalApplication p
    arrow d e f a S F A x parameter hws har hfType haType hsapp hvs hnf ha hns
  have hy := OriginalNeutralQuotientApplicationProof.finalApplication p
    arrow d e g a T G A y parameter hwt har hgType haType htapp hvt hng ha hnt
  exact andIntro hselectors (andIntro hrequirements (andIntro hstate
    (andIntro hpeeled (andIntro hchild (andIntro ha (andIntro hx hy))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientRecoveredProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientRecoveredProof
