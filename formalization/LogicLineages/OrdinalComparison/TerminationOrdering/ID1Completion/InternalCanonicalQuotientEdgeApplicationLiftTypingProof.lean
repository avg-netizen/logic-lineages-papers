module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTypingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTypingProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition InternalCanonicalQuotientEdgeApplicationLift
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalCanonicalDescentSelectionInternalProof
open InternalCanonicalResultFoldInvariantApplicationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem typedRename {β : Type} (data : Data) (x typ : OTerm α) (j : α → β) :
    (typedAccepted data x typ).relabel j = typedAccepted data (x.relabel j) (typ.relabel j) :=
  InternalCanonicalQuotientEdgeSelectionTypingProof.typedRename data x typ j

theorem applicationRename {β : Type} (data : Data) (out d e x a : OTerm α) (j : α → β) :
    (applicationGraph data out d e x a).relabel j =
      applicationGraph data (out.relabel j) (d.relabel j) (e.relabel j) (x.relabel j) (a.relabel j) :=
  graph4Rename _ _ _ _ _ _ _

/-- Recover C at the actual N(a) witness; the function is unchanged. -/
theorem applicationRecover (data : Data) (out d e x a b : OTerm α)
    (hj : Nonempty (Derivation body Gamma (applicationGraph data out d e x a)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalResultFoldCalibration.normalizer data) b a))) :
    Nonempty (Derivation body Gamma
      (graph4 (InternalCanonicalResultFoldCalibration.combine data) out d e x b)) := by
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons a Fin.elim0)))
  apply compositionRecover (InternalCanonicalResultFoldCalibration.combine data)
    ![.projection 0,.projection 1,.projection 2,
      .composition (InternalCanonicalResultFoldCalibration.normalizer data) (fun _ : Fin 1 => .projection 3)]
    out xs (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons b Fin.elim0)))) hj
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases
      (unaryValue (InternalCanonicalResultFoldCalibration.normalizer data) (.projection 3) b a xs hn
        (projectionValue 3 xs)) (fun k => Fin.elim0 k)))) i

theorem withRaw (data : Data) (arrow d e x a b raw out : OTerm α)
    (hx : Nonempty (Derivation body Gamma (typedAccepted data x arrow)))
    (ha : Nonempty (Derivation body Gamma (typedAccepted data a d)))
    (hm : Nonempty (Derivation body Gamma (graph1 data.member (suc z) e)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hn : Nonempty (Derivation body Gamma (graph1 (InternalCanonicalResultFoldCalibration.normalizer data) b a)))
    (hj : Nonempty (Derivation body Gamma (applicationGraph data out d e x a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application raw d e x b))) :
    Nonempty (Derivation body Gamma (typedAccepted data out e)) := by
  let R := data.oldEdge.targetRepresentative
  let V := (InternalCanonicalDescentSelection.validity data).sourceValid
  have hxf := typedRecover R V data.member x arrow hx
  have haf := typedRecover R V data.member a d ha
  obtain ⟨hc⟩ := InternalCanonicalResultFoldInvariantConsumerProof.actualOriginalCanonicalFoldOutputConsumer
    body data.oldValidity R data.member α Gamma b a d
  obtain ⟨hs⟩ := andIntro (andLeft (andRight haf)) (andLeft (andRight (andRight haf)))
  obtain ⟨hn'⟩ := hn
  have hb := (⟨Derivation.implicationElimination (Derivation.implicationElimination hc hs) hn'⟩ :
    Nonempty (Derivation body Gamma (InternalCanonicalResultFoldInvariant.successfulOutput
      data.oldValidity R data.member b a d)))
  have hv := rawValidity data.oldValidity data.member arrow d e x b raw har
    (andLeft (andRight (andRight hxf))) (andLeft (andRight (andRight hb))) hm
    (andLeft (andRight hxf)) (andLeft (andRight hb)) hp
  have hd := unaryRecover (InternalCanonicalResultFoldCalibration.leaf data) application out raw
    (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons b Fin.elim0))))
    (applicationRecover data out d e x a b hj ⟨hn'⟩) hp
  exact typedAccept R V data.member out e
    (andIntro hm (andIntro (descentValidity R V out raw hd hv)
      (andIntro (descentLeft R V out raw e hd hv (rawLeft d e x b raw hp))
        (descentFixed R V out raw hd hv))))

theorem withNormalizer (data : Data) (arrow d e x a b out : OTerm α)
    (hx : Nonempty (Derivation body Gamma (typedAccepted data x arrow)))
    (ha : Nonempty (Derivation body Gamma (typedAccepted data a d)))
    (hm : Nonempty (Derivation body Gamma (graph1 data.member (suc z) e)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hn : Nonempty (Derivation body Gamma (graph1 (InternalCanonicalResultFoldCalibration.normalizer data) b a)))
    (hj : Nonempty (Derivation body Gamma (applicationGraph data out d e x a))) :
    Nonempty (Derivation body Gamma (typedAccepted data out e)) := by
  apply programCases application (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons b Fin.elim0)))) _
  intro β j Delta raw hctx hp
  rw [typedRename]
  simp only [consTermRename,emptyRename] at hp
  have hx' := renameInto hx j Delta hctx
  have ha' := renameInto ha j Delta hctx
  have hm' := renameInto hm j Delta hctx
  have har' := renameInto har j Delta hctx
  have hn' := renameInto hn j Delta hctx
  have hj' := renameInto hj j Delta hctx
  simp only [typedRename] at hx' ha'
  simp only [graph1Rename,sucRelabel,zRelabel] at hm' hn'
  rw [graph2Rename] at har'
  rw [applicationRename] at hj'
  exact withRaw data (arrow.relabel j) (d.relabel j) (e.relabel j) (x.relabel j)
    (a.relabel j) (b.relabel j) raw (out.relabel j) hx' ha' hm' har' hn' hj' hp

theorem symbolicTypedOutput (data : Data) (arrow d e x a out : OTerm α)
    (hx : Nonempty (Derivation body Gamma (typedAccepted data x arrow)))
    (ha : Nonempty (Derivation body Gamma (typedAccepted data a d)))
    (hm : Nonempty (Derivation body Gamma (graph1 data.member (suc z) e)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hj : Nonempty (Derivation body Gamma (applicationGraph data out d e x a))) :
    Nonempty (Derivation body Gamma (typedAccepted data out e)) := by
  apply programCases (InternalCanonicalResultFoldCalibration.normalizer data) (Fin.cons a Fin.elim0) _
  intro β j Delta b hctx hn
  rw [typedRename]
  simp only [consTermRename,emptyRename] at hn
  have hx' := renameInto hx j Delta hctx
  have ha' := renameInto ha j Delta hctx
  have hm' := renameInto hm j Delta hctx
  have har' := renameInto har j Delta hctx
  have hj' := renameInto hj j Delta hctx
  simp only [typedRename] at hx' ha'
  simp only [graph1Rename,sucRelabel,zRelabel] at hm'
  rw [graph2Rename] at har'
  rw [applicationRename] at hj'
  exact withNormalizer data (arrow.relabel j) (d.relabel j) (e.relabel j) (x.relabel j)
    (a.relabel j) b (out.relabel j) hx' ha' hm' har' hn hj'

theorem applicationTypedOutput (S : List Ty) (data : Data)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S data.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty) (x a out : OTerm α)
    (hx : Nonempty (Derivation body Gamma (typedAccepted data x (numeral (typeNumber (.arrow sigma tau))))))
    (ha : Nonempty (Derivation body Gamma (typedAccepted data a (numeral (typeNumber sigma)))))
    (hj : Nonempty (Derivation body Gamma (applicationGraph data out
      (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x a))) :
    Nonempty (Derivation body Gamma (typedAccepted data out (numeral (typeNumber tau)))) := by
  have hxf := typedRecover data.oldEdge.targetRepresentative
    (InternalCanonicalDescentSelection.validity data).sourceValid data.member x
    (numeral (typeNumber (.arrow sigma tau))) hx
  exact symbolicTypedOutput data _ _ _ x a out hx ha
    (InternalTypedEdgePresentationSupportProof.codomainMembership S data.member hm hc sigma tau (andLeft hxf))
    (InternalTypedEdgePresentationSupportProof.arrowNumeral sigma tau) hj

theorem actualOriginalCanonicalApplicationTypedOutput :
    InternalCanonicalQuotientEdgeApplicationLiftTargets.ActualOriginalCanonicalApplicationTypedOutput := by
  intro S data hm hc body sigma tau α Delta x a out
  let P := applicationPremises data sigma tau x a out
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := applicationTypedOutput S data hm hc sigma tau x a out
    (andLeft hp) (andLeft (andRight hp)) (andRight (andRight hp))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTypingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTypingProof
