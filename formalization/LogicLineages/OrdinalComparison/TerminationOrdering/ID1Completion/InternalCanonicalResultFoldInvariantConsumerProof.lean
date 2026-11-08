module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantConsumerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalCanonicalResultFoldInvariant InternalCanonicalResultFoldInvariantTargets
open InternalCanonicalResultFoldInvariantSyntaxProof InternalCanonicalResultFoldInvariantBindingProof
open InternalCanonicalResultFoldInvariantInductionProof InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalCanonicalDescentSelectionInternalProof InternalBoundedDescentNormalizerSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Equality of actual N outputs transports all three invariant graphs,
including BOTH occurrences of the transition-fixed output. -/
theorem invariantOutputTransport (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (out other typ : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn out other)))
    (h : Nonempty (Derivation body Gamma (outputInvariant old R member out typ))) :
    Nonempty (Derivation body Gamma (outputInvariant old R member other typ)) :=
  andIntro (headTransport (validity old member) (suc z) out other Fin.elim0 he (andLeft h))
    (andIntro (headTransport InternalUnpair.left typ out other Fin.elim0 he (andLeft (andRight h)))
      (fixedTransport R (validity old member) out other he (andRight (andRight h))))

/-- Success comes from the internally constructed certified output, while
functionality identifies it with the consumer's supplied actual N output. -/
theorem consumerFromExistence (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (out input typ : OTerm α)
    (hx : Nonempty (Derivation body Gamma (hasCertifiedOutput old R member input typ)))
    (hn : Nonempty (Derivation body Gamma (foldGraph old R member out input))) :
    Nonempty (Derivation body Gamma (successfulOutput old R member out input typ)) := by
  apply hasCertifiedOutputCases old R member input typ _ hx
  intro β j Delta produced hj hc
  rw [successfulOutputRename]
  have hn' := renameInto hn j Delta hj
  rw [foldGraphRename] at hn'
  have he := valueUnique
    (InternalCanonicalResultFoldOpening.foldN R (validity old member) member)
    produced (out.relabel j) (Fin.cons (input.relabel j) Fin.elim0)
    (andRight (andLeft hc)) hn'
  exact andIntro (andLeft (andLeft hc))
    (invariantOutputTransport old R member produced (out.relabel j) (typ.relabel j) he (andRight hc))

theorem actualOriginalCanonicalFoldOutputConsumer :
    ActualOriginalCanonicalFoldOutputConsumer := by
  intro body old R member α Gamma out input typ
  let Delta := foldGraph old R member out input :: sourcePremises old member input typ :: Gamma
  have hs : Nonempty (Derivation body Delta (sourcePremises old member input typ)) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hn : Nonempty (Derivation body Delta (foldGraph old R member out input)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := consumerFromExistence old R member out input typ
    (certifiedOutputExists old R member input typ hs) hn
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

/-- Membership is an independent requested-type graph. The consumer never
infers it from the arbitrary original source leaves or source validity. -/
theorem actualOriginalCanonicalFoldTypedOutput : ActualOriginalCanonicalFoldTypedOutput := by
  intro body old R member α Gamma out input typ
  let Delta := foldGraph old R member out input ::
    graph1 member InternalOriginalStepGuard.one typ :: sourcePremises old member input typ :: Gamma
  have hs : Nonempty (Derivation body Delta (sourcePremises old member input typ)) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  have hm : Nonempty (Derivation body Delta (graph1 member InternalOriginalStepGuard.one typ)) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hn : Nonempty (Derivation body Delta (foldGraph old R member out input)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ho := consumerFromExistence old R member out input typ
    (certifiedOutputExists old R member input typ hs) hn
  obtain ⟨h⟩ := andIntro (andLeft ho)
    (typedAccept R (validity old member) member out typ (andIntro hm (andRight ho)))
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))⟩

theorem actualOriginalCanonicalFoldOutputContinuation :
    ActualOriginalCanonicalFoldOutputContinuation := by
  intro body old R member α Gamma input typ psi hs step
  exact hasCertifiedOutputCases old R member input typ psi
    (certifiedOutputExists old R member input typ hs) step

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantConsumerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantConsumerProof
