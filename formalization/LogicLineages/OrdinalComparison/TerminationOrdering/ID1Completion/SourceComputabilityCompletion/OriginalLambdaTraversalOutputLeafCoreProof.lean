module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLeafCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversalSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A source-valid actual transition fixed point is fixed by the SAME
selected leaf. This is proved from its bounded iteration, not assumed. -/
theorem selectedFixed (data : Data) (fixed parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity data)
        InternalOriginalStepGuard.one fixed parameter)))
    (hf : Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph data.oldRepresentative
        (InternalOriginalUniformDescentSelection.validity data) fixed fixed parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf data) fixed fixed parameter)) := by
  let V := InternalOriginalUniformDescentSelection.validity data
  let L := InternalParameterizedCanonicalResultFold.leaf data
  let T := InternalParameterizedBoundedDescentNormalizer.transition data.oldRepresentative V
  apply programCases L (Fin.cons fixed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta produced hj hl
  rw [graph2Rename]
  have hv' := renameInto hv j Theta hj
  have hf' := renameInto hf j Theta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv'
  rw [InternalParameterizedBoundedDescentNormalizerSyntaxProof.transitionRename] at hf'
  simp only [consTermRename,emptyRename] at hl
  have hn := InternalOriginalUniformDescentSelectionInternalProof.boundedRecover
    data.oldRepresentative V produced (fixed.relabel j) (parameter.relabel j) hl hv'
  have hr := InternalParameterizedBoundedDescentNormalizerSupportProof.normalizerRecover
    data.oldRepresentative V produced (fixed.relabel j) (parameter.relabel j) hn
  have hsame := InternalParameterizedNumericIterationLawsProof.fixedValue T (suc (fixed.relabel j))
    (fixed.relabel j) (parameter.relabel j) hf'
  have he := valueUnique (InternalParameterizedNumericIteration.repeatP T) produced (fixed.relabel j)
    (Fin.cons (suc (fixed.relabel j)) (Fin.cons (fixed.relabel j)
      (Fin.cons (parameter.relabel j) Fin.elim0))) hr hsame
  exact outputTransport L produced (fixed.relabel j)
    (Fin.cons (fixed.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hl

/-- Source validity, raw type, weak value decrease and actual selected-leaf
idempotence all follow independently of traversal or structural tags. -/
theorem leafOutput (rawData : Data) (window : Program 1)
    (out input typ parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter)))
    (hs : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window)
        input typ parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
          InternalOriginalStepGuard.one out parameter ⊓
        (graph1 InternalUnpair.left typ out ⊓
          (InternalParameterizedBoundedDescentNormalizer.atMost out input ⊓
            graph2 (leaf rawData window) out out parameter)))) := by
  let selected := leafData rawData window
  let R := selected.oldRepresentative
  let V := InternalOriginalUniformDescentSelection.validity selected
  have hv := andLeft hs
  have ho := InternalOriginalUniformDescentSelectionInternalProof.descentValidity
    R V out input parameter hl hv
  have ht := InternalOriginalUniformDescentSelectionInternalProof.descentLeft
    R V out input typ parameter hl hv (andRight hs)
  have hf := InternalOriginalUniformDescentSelectionInternalProof.descentFixed
    R V out input parameter hl hv
  have hd := InternalOriginalUniformDescentSelectionInternalProof.boundedRecover
    R V out input parameter hl hv
  obtain ⟨hb⟩ := InternalParameterizedBoundedDescentNormalizerProof.actualOriginalParameterizedBoundedDescentNormalizerBound
    body R V alpha Delta out input parameter
  obtain ⟨hd⟩ := hd
  exact andIntro ho (andIntro ht (andIntro ⟨Derivation.implicationElimination hb hd⟩
    (selectedFixed selected out parameter ho hf)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLeafCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLeafCoreProof
