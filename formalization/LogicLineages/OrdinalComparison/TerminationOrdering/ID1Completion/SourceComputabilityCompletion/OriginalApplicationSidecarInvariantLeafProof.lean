module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalApplicationSidecar OriginalApplicationSidecarInvariant OriginalApplicationSidecarInvariantSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
/-- The closed branch consumes the existing selected normalizer, not fixedness. -/
theorem leafInvariant (data : Data) (window : Program 1) (out input typ parameter : OrdinaryArithmetic.Term α)
    (hl : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (originalData data window)) out input parameter)))
    (hs : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.sourcePremises (originalData data window) input typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window out input typ parameter)) := by
  have hv := InternalApplicationStepPeelSupportProof.andLeft hs
  have ht := InternalApplicationStepPeelSupportProof.andRight hs
  have hd := InternalOriginalUniformDescentSelectionInternalProof.boundedRecover
    (originalData data window).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (originalData data window)) out input parameter hl hv
  have ho := InternalOriginalUniformDescentSelectionInternalProof.descentValidity
    (originalData data window).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (originalData data window)) out input parameter hl hv
  have hleft := InternalOriginalUniformDescentSelectionInternalProof.descentLeft
    (originalData data window).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (originalData data window)) out input typ parameter hl hv ht
  obtain ⟨hb⟩ := InternalParameterizedBoundedDescentNormalizerProof.actualOriginalParameterizedBoundedDescentNormalizerBound
    body (originalData data window).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (originalData data window)) α Gamma out input parameter
  obtain ⟨hd⟩ := hd
  exact InternalApplicationStepPeelSupportProof.andIntro ho (InternalApplicationStepPeelSupportProof.andIntro hleft ⟨Derivation.implicationElimination hb hd⟩)

/-- Recover the actual leaf output using its certified C graph and functionality. -/
theorem rejectedAtOutput (data : Data) (window : Program 1) (out input typ parameter : OrdinaryArithmetic.Term α)
    (hs : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.sourcePremises (originalData data window) input typ parameter)))
    (hf : Nonempty (Derivation body Gamma (graph2 (fold data window) out input parameter)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) z input parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window out input typ parameter)) := by
  apply programCases (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta produced hj hl
  rw [outputInvariantRename]
  simp only [consTermRename,emptyRename] at hl
  have hs' := renameInto hs j Delta hj
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesRename] at hs'
  have hf' := renameInto hf j Delta hj
  rw [graph2Rename] at hf'
  have hg' := renameInto hg j Delta hj
  simp only [graph2Rename,zRelabel] at hg'
  have hc := InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))
    (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    InternalParameterizedCanonicalResultFold.rawApplicationAt
    (input.relabel j) produced (parameter.relabel j) hg' hl
  have he := valueUnique (fold data window) produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (InternalApplicationStepPeelSupportProof.andRight hc) hf'
  have hl' := outputTransport (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hl
  exact leafInvariant data window (out.relabel j) (input.relabel j)
    (typ.relabel j) (parameter.relabel j) hl' hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantLeafProof
