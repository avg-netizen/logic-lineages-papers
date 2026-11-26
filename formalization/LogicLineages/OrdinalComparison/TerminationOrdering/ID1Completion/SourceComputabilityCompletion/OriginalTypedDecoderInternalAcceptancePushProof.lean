module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptancePushProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalFuelSingletonSupportProof OriginalTypedDecoderInternalFuelSingletonProof
open OriginalTypedDecoderInternalAcceptanceSyntaxProof OriginalTypedDecoderInternalAcceptanceStateProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof
open OriginalTypedDecoderInternalPushSyntaxProof
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem pushOneAccepted (H : Program 1) (mode : Nat) (out gamma typ raw : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPushOne out (numeral mode) gamma typ raw z)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H out))) :
    Nonempty (Derivation body Gamma (programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma])) := by
  apply stepPushOneCases out (numeral mode) gamma typ raw z _ hp
  intro beta j Delta ys hj fields
  simp only [programRename,oneRename,tripleRename]
  have ha' := renameInto ha j Delta hj
  rw [acceptedStateRename] at ha'
  have hr := andLeft fields
  simp only [numeralRename] at hr
  have hc := andLeft (andRight fields)
  simp only [zRelabel] at hc
  have hs := andRight (andRight fields)
  exact singletonToCheck H mode (out.relabel j) (ys 1) (ys 0) (gamma.relabel j)
    (typ.relabel j) (raw.relabel j) hs hc hr
    (acceptedStateAt H (out.relabel j) (ys 1) hs ha')

theorem acceptedPushOneCases (H : Program 1) (mode : Nat) (gamma typ raw : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Gamma (programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma])))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (StepPushOne out (numeral mode) (gamma.relabel j) (typ.relabel j) (raw.relabel j) z)) →
      Nonempty (Derivation body Delta (AcceptedState H out)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply singletonCases mode typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  have ha' := renameInto ha j Delta hj
  simp only [programRename,oneRename,tripleRename] at ha'
  have hw := checkToSingleton H mode state work request (gamma.relabel j) (typ.relabel j) (raw.relabel j)
    hs hc hr ha'
  have hp := stepPushOneIntro state (numeral mode) (gamma.relabel j) (typ.relabel j) (raw.relabel j) z
    (![request,work] : Fin 2 → OTerm beta) (andIntro hr (andIntro hc hs))
  exact step beta j Delta state hj hp (acceptedStateIntro H state work hs hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptancePushProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptancePushProof
