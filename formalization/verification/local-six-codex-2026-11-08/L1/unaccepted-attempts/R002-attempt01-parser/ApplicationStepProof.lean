module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationStepProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem impApply {P Q : Formula α} (h : Nonempty (Derivation body Delta (P.imp Q)))
    (hp : Nonempty (Derivation body Delta P)) : Nonempty (Derivation body Delta Q) := by
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination h hp⟩

theorem validityAtValue (P : Program 2) (i : Fin 4) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Delta (graph2 P (suc z) (xs i) (xs 3)))) :
    Nonempty (Derivation body Delta (programGraph (validityAt P i) (suc z) xs)) :=
  binaryValue P (.projection i) (.projection 3) (suc z) (xs i) (xs 3) xs h
    (projectionValue i xs) (projectionValue 3 xs)

theorem rawGuardsValue (data : Data) (s t k parameter tag : OTerm α)
    (hs : Nonempty (Derivation body Delta (graph2 (validity data) (suc z) s parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 (targetValidity data) (suc z) t parameter)))
    (hls : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag s)))
    (hlt : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag t))) :
    Nonempty (Derivation body Delta (programGraph (rawGuards data) (suc z) ![s,t,k,parameter])) := by
  let xs : Fin 4 → OTerm α := ![s,t,k,parameter]
  exact conjunctionAccept _ _ xs (validityAtValue (validity data) 0 xs hs)
    (conjunctionAccept _ _ xs (validityAtValue (targetValidity data) 1 xs ht)
      (sameAccept (leftOf (.projection 0)) (leftOf (.projection 1)) tag xs
        (unaryValue InternalUnpair.left (.projection 0) tag s xs hls (projectionValue 0 xs))
        (unaryValue InternalUnpair.left (.projection 1) tag t xs hlt (projectionValue 1 xs))))

/-- Preserve the actual selected W at original raw application parents.
The unchanged normalized core transports its FULL output. Every outer
validity/tag check, including target SOURCE validity, is rebuilt internally. -/
theorem applicationStep (data : Data) (oldStep : Program 4)
    (arrow d e s t a k sourceApp targetApp liftedStep parameter : OTerm α)
    (har : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)))
    (hls : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow s)))
    (hlt : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow t)))
    (hla : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d a)))
    (hend : Nonempty (Derivation body Delta
      (InternalParameterizedStructuralEndpointGuard.accepted
        (validity data) (targetValidity data) data.member d e s t a parameter)))
    (hsapp : Nonempty (Derivation body Delta (graph4 application sourceApp d e s a)))
    (htapp : Nonempty (Derivation body Delta (graph4 application targetApp d e t a)))
    (hk : Nonempty (Derivation body Delta (graph1 stepLift liftedStep k)))
    (hold : Nonempty (Derivation body Delta (stepAccepted data oldStep s t k parameter))) :
    Nonempty (Derivation body Delta
      (stepAccepted data oldStep sourceApp targetApp liftedStep parameter)) := by
  let endpoint := InternalParameterizedStructuralEndpointGuard.selectedEndpoint data
  let xs : Fin 4 → OTerm α := ![s,t,k,parameter]
  have houter := conjunctionRecover _ _ xs hold
  have hinner := conjunctionRecover _ _ xs (andLeft houter)
  have hpre := andIntro har (andIntro hls (andIntro hlt (andIntro hla
    (andIntro hend (andIntro hsapp (andIntro htapp hk))))))
  have heq := impApply
    (InternalParameterizedApplicationStepCheckerProof.actualParameterizedOriginalLiftedChecker
      body endpoint oldStep α Delta d e arrow s t a k sourceApp targetApp liftedStep (suc z) parameter) hpre
  have hcore := impApply (andRight heq) (andRight hinner)
  have hparents := InternalParameterizedStructuralEndpointGuardApplicationProof.applicationValue data
    arrow d e s t a sourceApp targetApp parameter
    (andIntro har (andIntro hend (andIntro hsapp htapp)))
  have hendFactors := InternalParameterizedStructuralEndpointGuardSupportProof.endpointRecover
    (validity data) (targetValidity data) data.member arrow d e s t a parameter har hend
  obtain ⟨_,hvt,_⟩ := TypingProof.stepParts data oldStep s t k parameter hold
  have htargetSource := InternalParameterizedCanonicalResultFoldOpeningProof.rawValidity data
    arrow d e t a targetApp parameter har hlt hla
    (andRight (andRight (andRight (andRight hendFactors)))) hvt
    (andLeft (andRight (andRight hendFactors))) htapp
  let ys : Fin 4 → OTerm α := ![sourceApp,targetApp,liftedStep,parameter]
  have hg := rawGuardsValue data sourceApp targetApp liftedStep parameter e
    (andLeft hparents) (andLeft (andRight hparents))
    (andLeft (andRight (andRight hparents))) (andRight (andRight (andRight hparents)))
  exact conjunctionAccept _ _ ys
    (conjunctionAccept _ _ ys hg hcore)
    (validityAtValue (validity data) 1 ys htargetSource)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationStepProof
