module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTypingProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition InternalCanonicalQuotientEdgeSelection
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof InternalCanonicalResultFoldInvariantConsumerProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem typedRename {β : Type} (data : InternalCanonicalDescentSelection.Data)
    (x typ : OTerm α) (j : α → β) :
    (typedAccepted data x typ).relabel j = typedAccepted data (x.relabel j) (typ.relabel j) := by
  simp only [typedAccepted, InternalCanonicalDescentSelection.typedAccepted, graph2Rename,
    InternalOriginalStepGuard.one, sucRelabel, zRelabel]

theorem edgeRename {β : Type} (data : InternalCanonicalDescentSelection.Data)
    (x y c : OTerm α) (j : α → β) :
    (edgeAccepted data x y c).relabel j =
      edgeAccepted data (x.relabel j) (y.relabel j) (c.relabel j) := by
  simp only [edgeAccepted, InternalQuotientEdgeChecker.accepted, graph3Rename, sucRelabel, zRelabel]

/-- The source validity comes from the actual original step guard. -/
theorem sourceValidity (data : InternalCanonicalDescentSelection.Data) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (InternalOriginalApplicationStep.accepted (baseData data) s t k))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalDescentSelection.validity data).sourceValid (suc z) s)) := by
  let xs : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  have ho := conjunctionRecover (InternalOriginalStepGuard.guards
      (InternalOriginalApplicationStep.validity (baseData data)))
    (InternalOriginalApplicationStep.normalizedCore (baseData data)) xs h
  have hg := conjunctionRecover
    (InternalOriginalStepGuard.sourceAt (InternalOriginalApplicationStep.validity (baseData data)))
    (InternalAcceptance.conjunction
      (InternalOriginalStepGuard.targetAt (InternalOriginalApplicationStep.validity (baseData data)))
      InternalOriginalStepGuard.sameOuterTypes) xs (andLeft ho)
  exact InternalOriginalStepGuardSupportProof.atRecover
    (InternalCanonicalDescentSelection.validity data).sourceValid 0 (suc z) xs (andLeft hg)

/-- The exact-one source branch exposes N, without external calibration. -/
theorem sourceFold (data : InternalCanonicalDescentSelection.Data) (x s : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalDescentSelection.validity data).sourceValid (suc z) s)))
    (hn : Nonempty (Derivation body Gamma (graph1 (edgeData data).sourceRepresentative x s))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalResultFoldCalibration.normalizer data) x s)) := by
  let V := (InternalCanonicalDescentSelection.validity data).sourceValid
  let xs : Fin 1 → OTerm α := Fin.cons s Fin.elim0
  exact successorBranchElim (InternalApplicationValidityStack.exactOne V)
    (InternalAcceptance.constantZero 1) (InternalCanonicalResultFoldCalibration.normalizer data)
    x z xs
    (InternalApplicationStepPeelSupportProof.sameAccept V
      (InternalLessThan.constantOne 1) (suc z) xs hv
      (InternalLessThanSupportProof.oneConstantValue xs)) hn

/-- A symbolic raw tag is identified with the requested type by functionality
of the original left selector at the actual fold output. -/
theorem rawWithTag (data : InternalCanonicalDescentSelection.Data)
    (x y s t k typ tag : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ)))
    (he : Nonempty (Derivation body Gamma
      (InternalQuotientEdgeChecker.requirements (edgeData data) x y s t k)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ)) := by
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
  have hsource := outputTransport InternalUnpair.left tag typ (Fin.cons s Fin.elim0) htag hl
  have hguard := InternalOriginalStepGuardSupportProof.taggedRecover
    (InternalOriginalApplicationStep.validity (baseData data))
    (InternalOriginalApplicationStep.normalizedCore (baseData data)) typ s t k hsource (andLeft hw)
  obtain ⟨hconsumer⟩ := actualOriginalCanonicalFoldTypedOutput body data.oldValidity
    data.oldEdge.targetRepresentative data.member α Gamma y t typ
  obtain ⟨hinput⟩ := andIntro (andRight hw) (andLeft (andRight (andRight hguard)))
  obtain ⟨hmember⟩ := andLeft hf
  obtain ⟨houtput⟩ := andRight (andRight he)
  exact andRight ⟨Derivation.implicationElimination
    (Derivation.implicationElimination (Derivation.implicationElimination hconsumer hinput) hmember) houtput⟩

/-- Query the original left Program internally; no raw tag is a premise. -/
theorem rawTyped (data : InternalCanonicalDescentSelection.Data) (x y c s t k typ : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data x y c)))
    (hf : Nonempty (Derivation body Gamma (selectors c s t k))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ)) := by
  apply programCases InternalUnpair.left (Fin.cons s Fin.elim0) _
  intro β j Delta tag hj hl
  rw [typedRename]
  simp only [consTermRename, emptyRename] at hl
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hf' := renameInto hf j Delta hj
  rw [selectorsRename] at hf'
  exact rawWithTag data (x.relabel j) (y.relabel j) (s.relabel j) (t.relabel j)
    (k.relabel j) (typ.relabel j) tag ht'
    (InternalQuotientEdgeCheckerSupportProof.checkerRecover (edgeData data)
      (x.relabel j) (y.relabel j) (c.relabel j) (s.relabel j) (t.relabel j) (k.relabel j) hf' he') hl

/-- Eliminate the actual step selector output in the internally extended context. -/
theorem withSourceTarget (data : InternalCanonicalDescentSelection.Data) (x y c s t typ : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data x y c)))
    (hs : Nonempty (Derivation body Gamma (graph1 source s c)))
    (hv : Nonempty (Derivation body Gamma (graph1 target t c))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ)) := by
  apply programCases step (Fin.cons c Fin.elim0) _
  intro β j Delta k hj hk
  rw [typedRename]
  simp only [consTermRename, emptyRename] at hk
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  have hv' := renameInto hv j Delta hj
  rw [graph1Rename] at hv'
  exact rawTyped data (x.relabel j) (y.relabel j) (c.relabel j)
    (s.relabel j) (t.relabel j) k (typ.relabel j) ht' he' (andIntro hs' (andIntro hv' hk))

theorem withSource (data : InternalCanonicalDescentSelection.Data) (x y c s typ : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data x y c)))
    (hs : Nonempty (Derivation body Gamma (graph1 source s c))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ)) := by
  apply programCases target (Fin.cons c Fin.elim0) _
  intro β j Delta t hj hv
  rw [typedRename]
  simp only [consTermRename, emptyRename] at hv
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  exact withSourceTarget data (x.relabel j) (y.relabel j) (c.relabel j)
    (s.relabel j) t (typ.relabel j) ht' he' hs' hv

theorem typedPropagation (data : InternalCanonicalDescentSelection.Data) (x y c typ : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data x y c))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ)) := by
  apply programCases source (Fin.cons c Fin.elim0) _
  intro β j Delta s hj hs
  rw [typedRename]
  simp only [consTermRename, emptyRename] at hs
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  exact withSource data (x.relabel j) (y.relabel j) (c.relabel j) s (typ.relabel j) ht' he' hs

theorem actualOriginalCanonicalEdgeTypedPropagation :
    InternalCanonicalQuotientEdgeSelectionTargets.ActualOriginalCanonicalEdgeTypedPropagation := by
  intro body data α Delta x y certificate typ
  let Gamma := (typedAccepted data x typ ⊓ edgeAccepted data x y certificate) :: Delta
  have hp : Nonempty (Derivation body Gamma
      (typedAccepted data x typ ⊓ edgeAccepted data x y certificate)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := typedPropagation data x y certificate typ (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTypingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTypingProof
