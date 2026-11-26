module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem leftComponent (P Q : Program 2) (input parameter out a : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left a out)))
    (hr : Nonempty (Derivation body Delta (graph2 (pairOf P Q) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 P a input parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons out Fin.elim0) _
  intro beta j Theta b hj hb
  rw [graph2Rename]
  have hl' := renameInto hl j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hl'
  rw [graph2Rename] at hr'
  simp only [consTermRename,emptyRename] at hb
  have hp := InternalApplicationCertificateConstructorsSupportProof.reconstructPair
    (out.relabel j) (a.relabel j) b hl' hb
  exact andLeft (OriginalHereditaryObservationLayerInternalProof.pairComponents P Q
    (input.relabel j) (parameter.relabel j) (out.relabel j) (a.relabel j) b hp hr')

theorem rightComponent (P Q : Program 2) (input parameter out b : OTerm alpha)
    (hright : Nonempty (Derivation body Delta (graph1 InternalUnpair.right b out)))
    (hr : Nonempty (Derivation body Delta (graph2 (pairOf P Q) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 Q b input parameter)) := by
  apply programCases InternalUnpair.left (Fin.cons out Fin.elim0) _
  intro beta j Theta a hj ha
  rw [graph2Rename]
  have hb' := renameInto hright j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hb'
  rw [graph2Rename] at hr'
  simp only [consTermRename,emptyRename] at ha
  have hp := InternalApplicationCertificateConstructorsSupportProof.reconstructPair
    (out.relabel j) a (b.relabel j) ha hb'
  exact andRight (OriginalHereditaryObservationLayerInternalProof.pairComponents P Q
    (input.relabel j) (parameter.relabel j) (out.relabel j) a (b.relabel j) hp hr')

theorem recursiveRoot (R : Program 2) (H G : Program 1) (M W : Program 2)
    (input parameter out inner root : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out input parameter)))
    (hi : Nonempty (Derivation body Delta (graph1 InternalUnpair.right inner out)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left root inner))) :
    Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation
      (OriginalHereditaryEvaluatorDefinitions.evaluator R)) root input parameter)) := by
  obtain ⟨he⟩ := EvaluatorLayerProof.actual R H G M W body alpha Delta input parameter out hs
  obtain ⟨hv⟩ := hv
  have hlayer := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft he) hv)
  have hinner := rightComponent _ _ input parameter out inner hi hlayer
  exact leftComponent _ _ input parameter inner root hr hinner

theorem lambdaBranch (R : Program 2) (input parameter out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) input parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.lambda R) out input parameter)) := by
  apply programCases (OriginalRootObservation.lambda R) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hvalue
  rw [graph2Rename]
  have ht' := renameInto ht j Theta hj
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht' hv'
  simp only [consTermRename,emptyRename] at hvalue
  have hroot := OriginalRootObservationInternalSupportProof.dispatch1 R
    (input.relabel j) (parameter.relabel j) value ht' hvalue
  have he := valueUnique (OriginalRootObservation.rootObservation R) value (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hroot hv'
  exact outputTransport (OriginalRootObservation.lambda R) value (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hvalue

theorem applicationBranch (R : Program 2) (input parameter out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) input parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.application R) out input parameter)) := by
  apply programCases (OriginalRootObservation.application R) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hvalue
  rw [graph2Rename]
  have ht' := renameInto ht j Theta hj
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht' hv'
  simp only [consTermRename,emptyRename] at hvalue
  have hroot := OriginalRootObservationInternalSupportProof.dispatch2 R
    (input.relabel j) (parameter.relabel j) value ht' hvalue
  have he := valueUnique (OriginalRootObservation.rootObservation R) value (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hroot hv'
  exact outputTransport (OriginalRootObservation.application R) value (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hvalue
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
