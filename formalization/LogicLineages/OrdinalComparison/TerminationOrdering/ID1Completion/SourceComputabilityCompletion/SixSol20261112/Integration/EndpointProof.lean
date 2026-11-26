module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.EndpointProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalParameterizedStructuralEndpointGuard
open InternalParameterizedStructuralEndpointGuardSupportProof (atValue atRecover)
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalTransparentLambdaFinalLogicProof
open OriginalFinalVariableCanonicalSupportProof (iffForward iffBackward)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentDecoderValidatorCollapse (GraphEquality)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Exact-one conjunction has literal zero/one outputs; graph equivalence of
its two acceptance tests consequently transports every output. -/
theorem conjunctionCongruence {n : Nat} (p q r s : Program n)
    (xs : Fin n → OTerm alpha) (out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      ((programGraph p (numeral 1) xs).iff (programGraph r (numeral 1) xs))))
    (hq : Nonempty (Derivation body Delta
      ((programGraph q (numeral 1) xs).iff (programGraph s (numeral 1) xs)))) :
    Nonempty (Derivation body Delta
      ((programGraph (InternalAcceptance.conjunction p q) out xs).iff
        (programGraph (InternalAcceptance.conjunction r s) out xs))) :=
  iffCompose (conjunctionEquation p q xs out)
    (iffCompose (booleanIff out (andIff hp hq))
      (iffReverse (conjunctionEquation r s xs out)))

/-- Each composition reads the identical selected coordinate and actual
parameter. Functionality or successful native execution is unnecessary. -/
theorem atCongruence (p q : Program 2) (i : Fin 6)
    (out : OTerm alpha) (xs : Fin 6 → OTerm alpha)
    (he : ∀ (Theta : List (Formula alpha)),
      Nonempty (Derivation body Theta
        ((graph2 p out (xs i) (xs 5)).iff (graph2 q out (xs i) (xs 5))))) :
    Nonempty (Derivation body Delta
      ((programGraph (atParameter p i) out xs).iff
        (programGraph (atParameter q i) out xs))) := by
  let A := programGraph (atParameter p i) out xs
  let B := programGraph (atParameter q i) out xs
  have ha : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (B :: Delta) B) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := atValue q i out xs
    (iffForward (he (A :: Delta)) (atRecover p i out xs ha))
  obtain ⟨hr⟩ := atValue p i out xs
    (iffBackward (he (B :: Delta)) (atRecover q i out xs hb))
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hr)⟩

/-- All original endpoint tests are retained, including the unfiltered
packed-target test and the same type-guard Program. -/
theorem endpointCongruence (source target source' target' member : Program 2)
    (hs : GraphEquality source source') (ht : GraphEquality target target')
    (out d e s t a parameter : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((graph6 (endpoint source target member) out d e s t a parameter).iff
        (graph6 (endpoint source' target' member) out d e s t a parameter))) := by
  let xs : Fin 6 → OTerm alpha := ![d,e,s,t,a,parameter]
  have hs2 := atCongruence (body := body) (Delta := Delta) source source' 2 (numeral 1) xs
    (fun Theta => hs body alpha Theta (numeral 1) (xs 2) (xs 5))
  have ht3 := atCongruence (body := body) (Delta := Delta) target target' 3 (numeral 1) xs
    (fun Theta => ht body alpha Theta (numeral 1) (xs 3) (xs 5))
  have hs4 := atCongruence (body := body) (Delta := Delta) source source' 4 (numeral 1) xs
    (fun Theta => hs body alpha Theta (numeral 1) (xs 4) (xs 5))
  have htail := iffSelf (body := body) (Gamma := Delta)
    (programGraph (InternalAcceptance.conjunction typeGuard (atParameter member 1)) (numeral 1) xs)
  have hargument := conjunctionCongruence
    (atParameter source 4) (InternalAcceptance.conjunction typeGuard (atParameter member 1))
    (atParameter source' 4) (InternalAcceptance.conjunction typeGuard (atParameter member 1))
    xs (numeral 1) hs4 htail
  have htarget := conjunctionCongruence
    (atParameter target 3)
    (InternalAcceptance.conjunction (atParameter source 4)
      (InternalAcceptance.conjunction typeGuard (atParameter member 1)))
    (atParameter target' 3)
    (InternalAcceptance.conjunction (atParameter source' 4)
      (InternalAcceptance.conjunction typeGuard (atParameter member 1)))
    xs (numeral 1) ht3 hargument
  exact conjunctionCongruence _ _ _ _ xs out hs2 htarget

theorem selectedMember (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    (OriginalTransparentDecoderValidatorCollapse.selected p H G W).member =
      OriginalMixedLiteralEndpointDefinitions.memberAt
        (InternalOriginalUniformContextMembership.contextMember p.base.member) := by
  change (OriginalLambdaTraversalSelection.finalData
    (OriginalTransparentDecoderValidatorCollapse.refined p H G W)).member = _
  rw [OriginalLambdaTraversalSelectionFieldProof.sameMember,
    OriginalLambdaTraversalSelectionFieldProof.leafMember]
  rfl

theorem actualFinalEndpoint : ActualFinalEndpoint := by
  intro p H G W body alpha Delta out d e s t a parameter
  have hs := OriginalTransparentDecoderValidatorCollapseProof.actualOriginalTransparentDecoderFinalSourceCollapse p H G W
  have ht := OriginalTransparentDecoderValidatorCollapseProof.actualOriginalTransparentDecoderFinalTargetCollapse p H G W
  change Nonempty (Derivation body Delta
    ((graph6 (endpoint
      (InternalOriginalUniformDescentSelection.validity
        (OriginalTransparentDecoderValidatorCollapse.selected p H G W))
      (InternalOriginalUniformDescentSelection.targetValidity
        (OriginalTransparentDecoderValidatorCollapse.selected p H G W))
      (OriginalTransparentDecoderValidatorCollapse.selected p H G W).member)
      out d e s t a parameter).iff
    (graph6 (endpoint
      (OriginalUniverseDecoder.source H G
        (InternalOriginalUniformContextMembership.contextMember p.base.member) W)
      (OriginalTypedDecoder.target H G)
      (OriginalMixedLiteralEndpointDefinitions.memberAt
        (InternalOriginalUniformContextMembership.contextMember p.base.member)))
      out d e s t a parameter)))
  rw [selectedMember]
  exact endpointCongruence _ _ _ _ _ hs ht out d e s t a parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.EndpointProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.EndpointProof
