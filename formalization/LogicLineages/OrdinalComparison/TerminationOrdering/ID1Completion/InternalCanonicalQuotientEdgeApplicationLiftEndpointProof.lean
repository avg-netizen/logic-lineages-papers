module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTypingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEndpointProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition InternalCanonicalQuotientEdgeSelection
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalApplicationStepPeelSupportProof
open InternalCanonicalResultFoldInvariantConsumerProof InternalCanonicalQuotientEdgeSelectionTypingProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def endpointFacts (data : InternalCanonicalDescentSelection.Data)
    (arrow d e s t a : OTerm α) : Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (InternalStructuralEndpointGuard.accepted (InternalCanonicalDescentSelection.validity data)
      data.member d e s t a ⊓
      (InternalStructuralEndpointGuard.requirements (InternalCanonicalDescentSelection.validity data)
        data.member arrow d e s t a ⊓
        graph1 (InternalCanonicalDescentSelection.validity data).sourceValid
          InternalOriginalStepGuard.one t))

/-- Recover a raw source tag from the actual fold output, never from old R-tag rules. -/
theorem rawSourceWithTag (data : InternalCanonicalDescentSelection.Data)
    (x y s t k typ tag : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ)))
    (he : Nonempty (Derivation body Gamma
      (InternalQuotientEdgeChecker.requirements (edgeData data) x y s t k)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ s)) := by
  have hw := InternalCanonicalQuotientEdgeSelectionSupportProof.stepRecover data s t k (andLeft he)
  have hs := sourceValidity data s t k (andLeft hw)
  have hn := sourceFold data x s hs (andLeft (andRight he))
  obtain ⟨hc⟩ := actualOriginalCanonicalFoldOutputConsumer body data.oldValidity
    data.oldEdge.targetRepresentative data.member α Gamma x s tag
  obtain ⟨hp⟩ := andIntro hs hl
  obtain ⟨hn⟩ := hn
  have ho := (⟨Derivation.implicationElimination
    (Derivation.implicationElimination hc hp) hn⟩ : Nonempty (Derivation body Gamma
      (InternalCanonicalResultFoldInvariant.successfulOutput data.oldValidity
        data.oldEdge.targetRepresentative data.member x s tag)))
  have hf := InternalCanonicalDescentSelectionInternalProof.typedRecover
    data.oldEdge.targetRepresentative (InternalCanonicalDescentSelection.validity data).sourceValid
    data.member x typ ht
  have htag := valueUnique InternalUnpair.left tag typ (Fin.cons x Fin.elim0)
    (andLeft (andRight (andRight ho))) (andLeft (andRight (andRight hf)))
  exact outputTransport InternalUnpair.left tag typ (Fin.cons s Fin.elim0) htag hl

theorem rawSourceTag (data : InternalCanonicalDescentSelection.Data)
    (x y c s t k typ : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data x y c)))
    (hf : Nonempty (Derivation body Gamma (selectors c s t k))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ s)) := by
  apply programCases InternalUnpair.left (Fin.cons s Fin.elim0) _
  intro β j Delta tag hj hl
  rw [graph1Rename]
  simp only [consTermRename, emptyRename] at hl
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hf' := renameInto hf j Delta hj
  rw [selectorsRename] at hf'
  exact rawSourceWithTag data (x.relabel j) (y.relabel j) (s.relabel j) (t.relabel j)
    (k.relabel j) (typ.relabel j) tag ht'
    (InternalQuotientEdgeCheckerSupportProof.checkerRecover (edgeData data)
      (x.relabel j) (y.relabel j) (c.relabel j) (s.relabel j) (t.relabel j) (k.relabel j) hf' he') hl

/-- All raw validity and tag facts are derived from the actual selected W and N. -/
theorem endpointFromCore (S : List Ty) (data : InternalCanonicalDescentSelection.Data)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S data.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (x y a certificate out other s t k : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (InternalCanonicalQuotientEdgeApplicationLift.corePremises data sigma tau
        x y a certificate out other)))
    (hselectors : Nonempty (Derivation body Gamma (selectors certificate s t k))) :
    Nonempty (Derivation body Gamma (endpointFacts data
      (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
      (numeral (typeNumber tau)) s t a)) := by
  have hx := InternalCanonicalDescentSelectionInternalProof.typedRecover
    data.oldEdge.targetRepresentative (InternalCanonicalDescentSelection.validity data).sourceValid
    data.member x (numeral (typeNumber (.arrow sigma tau))) (andLeft hp)
  have ha := InternalCanonicalDescentSelectionInternalProof.typedRecover
    data.oldEdge.targetRepresentative (InternalCanonicalDescentSelection.validity data).sourceValid
    data.member a (numeral (typeNumber sigma)) (andLeft (andRight hp))
  have he := andLeft (andRight (andRight hp))
  have hedge := InternalQuotientEdgeCheckerSupportProof.checkerRecover (edgeData data)
    x y certificate s t k hselectors he
  have hw := InternalCanonicalQuotientEdgeSelectionSupportProof.stepRecover data s t k (andLeft hedge)
  have hs := sourceValidity data s t k (andLeft hw)
  have hsource := rawSourceTag data x y certificate s t k
    (numeral (typeNumber (.arrow sigma tau))) (andLeft hp) he hselectors
  have hg := InternalOriginalStepGuardSupportProof.taggedRecover
    (InternalOriginalApplicationStep.validity (baseData data))
    (InternalOriginalApplicationStep.normalizedCore (baseData data))
    (numeral (typeNumber (.arrow sigma tau))) s t k hsource (andLeft hw)
  have htags : Nonempty (Derivation body Gamma
      (InternalStructuralEndpointGuard.tagGraphs
        (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma)) s t a)) :=
    andIntro hsource (andIntro (andLeft (andRight (andRight hg)))
      (andLeft (andRight (andRight ha))))
  have har := InternalTypedEdgePresentationSupportProof.arrowNumeral
    (body := body) (Gamma := Gamma) (α := α) sigma tau
  have hmemb := InternalTypedEdgePresentationSupportProof.codomainMembership
    S data.member hm hc sigma tau (andLeft hx)
  have hr : Nonempty (Derivation body Gamma
      (InternalStructuralEndpointGuard.requirements (InternalCanonicalDescentSelection.validity data)
        data.member (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
        (numeral (typeNumber tau)) s t a)) :=
    andIntro hs (andIntro (andLeft (andRight hg))
      (andIntro (andLeft (andRight ha)) (andIntro htags hmemb)))
  have hep := InternalStructuralEndpointGuardSupportProof.endpointAccept
    (InternalCanonicalDescentSelection.validity data) data.member
    (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
    (numeral (typeNumber tau)) s t a har hr
  exact andIntro har (andIntro hep (andIntro hr (andRight hw)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEndpointProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEndpointProof
