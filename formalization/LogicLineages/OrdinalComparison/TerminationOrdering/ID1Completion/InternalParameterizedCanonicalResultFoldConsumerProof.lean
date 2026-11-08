module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldTargets
open InternalParameterizedCanonicalResultFoldSyntaxProof InternalParameterizedCanonicalResultFoldBindingProof
open InternalParameterizedCanonicalResultFoldInductionProof InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem invariantOutputTransport (data : Data) (out other typ parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn out other)))
    (h : Nonempty (Derivation body Gamma (outputInvariant data out typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data other typ parameter)) :=
  andIntro (headTransport (validity data) (suc z) out other (Fin.cons parameter Fin.elim0) he (andLeft h))
    (andIntro (headTransport InternalUnpair.left typ out other Fin.elim0 he (andLeft (andRight h)))
      (InternalParameterizedBoundedDescentNormalizerSupportProof.fixedTransport
        data.oldRepresentative (validity data) out other parameter he (andRight (andRight h))))

/-- Program functionality identifies the supplied raw N output with the
internally produced certified witness, including both occurrences in T. -/
theorem consumerFromExistence (data : Data) (out input typ parameter : OTerm α)
    (hx : Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data out input parameter))) :
    Nonempty (Derivation body Gamma (successfulOutput data out input typ parameter)) := by
  apply hasCertifiedOutputCases data input typ parameter _ hx
  intro β j Delta produced hj hc
  rw [successfulOutputRename]
  have hn' := renameInto hn j Delta hj
  rw [foldGraphRename] at hn'
  have he := valueUnique (foldN data) produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (andRight (andLeft hc)) hn'
  exact andIntro (andLeft (andLeft hc))
    (invariantOutputTransport data produced (out.relabel j) (typ.relabel j)
      (parameter.relabel j) he (andRight hc))

theorem certifiedAt (data : Data) (out input typ parameter : OTerm α)
    (hv : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ input)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data out input parameter))) :
    Nonempty (Derivation body Gamma (certifiedOutput data out input typ parameter)) := by
  have hs := consumerFromExistence data out input typ parameter
    (certifiedOutputExists data input typ parameter (andIntro hv hl)) hn
  exact andIntro (andIntro (andLeft hs) hn) (andRight hs)

theorem actualParameterizedCanonicalFoldOutputInvariant : ActualParameterizedCanonicalFoldOutputInvariant := by
  intro body data α Gamma out input typ parameter
  let Delta := foldGraph data out input parameter :: sourcePremises data input typ parameter :: Gamma
  have hs : Nonempty (Derivation body Delta (sourcePremises data input typ parameter)) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hn : Nonempty (Derivation body Delta (foldGraph data out input parameter)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := consumerFromExistence data out input typ parameter
    (certifiedOutputExists data input typ parameter hs) hn
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

theorem actualParameterizedCanonicalFoldTypedOutput : ActualParameterizedCanonicalFoldTypedOutput := by
  intro body data α Gamma out input typ parameter
  let Delta := foldGraph data out input parameter ::
    graph2 data.member InternalOriginalStepGuard.one typ parameter ::
      sourcePremises data input typ parameter :: Gamma
  have hs : Nonempty (Derivation body Delta (sourcePremises data input typ parameter)) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  have hm : Nonempty (Derivation body Delta
      (graph2 data.member InternalOriginalStepGuard.one typ parameter)) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hn : Nonempty (Derivation body Delta (foldGraph data out input parameter)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ho := consumerFromExistence data out input typ parameter
    (certifiedOutputExists data input typ parameter hs) hn
  obtain ⟨h⟩ := andIntro (andLeft ho)
    (InternalOriginalUniformDescentSelectionInternalProof.typedAccept
      data.oldRepresentative (validity data) data.member out typ parameter (andIntro hm (andRight ho)))
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
