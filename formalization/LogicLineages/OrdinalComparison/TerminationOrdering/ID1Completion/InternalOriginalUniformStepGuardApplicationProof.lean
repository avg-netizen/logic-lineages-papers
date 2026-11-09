module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformStepGuard InternalOriginalUniformStepGuardSupportProof
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalOriginalStepGuard (one)
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Every new guard comes from the original endpoint and recursive
validator clauses. The selected step core uses its checked graph equation;
no semantic statement is reflected into the calculus. -/
theorem applicationStep (data : Data) (oldStep : Program 4)
    (arrow d e s t a k sourceApp targetApp liftedStep parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftPremises data arrow d e s t a k sourceApp targetApp liftedStep parameter)))
    (hw : Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k parameter))) :
    Nonempty (Derivation body Gamma
      (stepAccepted data oldStep sourceApp targetApp liftedStep parameter)) := by
  have he := andLeft hp
  have har := andLeft he
  have hend := andLeft (andRight he)
  have hsapp := andLeft (andRight (andRight he))
  have htapp := andRight (andRight (andRight he))
  have hr := InternalParameterizedStructuralEndpointGuardSupportProof.endpointRecover
    (validity data) (targetValidity data) data.member arrow d e s t a parameter har hend
  have htags := andLeft (andRight (andRight (andRight hr)))
  have hm := andRight (andRight (andRight (andRight hr)))
  have ha := andLeft (andRight (andRight hr))
  have hwp := stepRecover data oldStep s t k parameter hw
  have hparts := guardedParts (validity data) (targetValidity data)
    (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep)
    s t k parameter (andLeft hwp)
  have hcore := andRight (andRight (andRight hparts))
  have hlift : Nonempty (Derivation body Gamma
      (InternalParameterizedApplicationStepChecker.liftedCheckerPremises
        (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
        d e arrow s t a k sourceApp targetApp liftedStep parameter)) :=
    andIntro har (andIntro (andLeft htags)
      (andIntro (andLeft (andRight htags))
        (andIntro (andRight (andRight htags))
          (andIntro hend (andIntro hsapp (andIntro htapp (andRight hp)))))))
  have hcoreApp := InternalParameterizedApplicationStepCheckerGraphProof.checkerBackward
    (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) oldStep
    d e arrow s t a k sourceApp targetApp liftedStep one parameter hlift hcore
  have happ := InternalParameterizedStructuralEndpointGuardApplicationProof.applicationValue
    data arrow d e s t a sourceApp targetApp parameter he
  have htSource := InternalParameterizedCanonicalResultFoldOpeningProof.rawValidity
    data arrow d e t a targetApp parameter har (andLeft (andRight htags))
    (andRight (andRight htags)) hm (andRight hwp) ha htapp
  apply stepAccept data oldStep sourceApp targetApp liftedStep parameter
  · exact taggedAccept (validity data) (targetValidity data)
      (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep)
      e sourceApp targetApp liftedStep parameter
      (andLeft (andRight (andRight happ)))
      (andIntro (andLeft happ) (andIntro (andLeft (andRight happ))
        (andIntro (andRight (andRight (andRight happ))) hcoreApp)))
  · exact htSource

theorem actualParameterizedCanonicalStepApplication :
    InternalOriginalUniformStepGuardTargets.ActualParameterizedCanonicalStepApplication := by
  intro body data oldStep α Delta arrow d e s t a k sourceApp targetApp liftedStep parameter
  let P := liftPremises data arrow d e s t a k sourceApp targetApp liftedStep parameter ⊓
    stepAccepted data oldStep s t k parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := applicationStep data oldStep arrow d e s t a k sourceApp targetApp liftedStep
    parameter (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardApplicationProof
