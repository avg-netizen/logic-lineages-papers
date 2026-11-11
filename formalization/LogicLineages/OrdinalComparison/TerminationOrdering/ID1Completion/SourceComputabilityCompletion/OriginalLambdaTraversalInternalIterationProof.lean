module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalEmptyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open InternalNumericIterationSupportProof InternalNumericIterationFixedPointProof InternalNumericIterationFusionProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundCoreProof (weakGapCases)
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem iterateEmpty (leaf : Program 2) (count state stack : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph1 emptyState state stack))) :
    Nonempty (Derivation positive Delta (graph2 (iterate leaf) state count state)) :=
  fixedValue (transition leaf) count state
    (OriginalLambdaTraversalInternalEmptyProof.emptyFixed leaf stack state hs)

theorem iterateOne (leaf : Program 2) (state out : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Delta (graph2 (iterate leaf) out (suc z) state)) :=
  repeatSuccValue (transition leaf) z state out state (repeatZeroValue (transition leaf) state) h

theorem iterateAfterFirst (leaf : Program 2) (count state next out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph1 (transition leaf) next state)))
    (hr : Nonempty (Derivation positive Delta (graph2 (iterate leaf) out count next))) :
    Nonempty (Derivation positive Delta (graph2 (iterate leaf) out (suc count) state)) := by
  have hsum := fusionValue (transition leaf) (suc z) count state next out (iterateOne leaf state next hf) hr
  have he : Derivation positive Delta (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  exact headTransport (iterate leaf) out (add (suc z) count) (suc count)
    (Fin.cons state Fin.elim0) ⟨he⟩ hsum

theorem iterateAfterLast (leaf : Program 2) (count state previous out : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph2 (iterate leaf) previous count state)))
    (hl : Nonempty (Derivation positive Delta (graph1 (transition leaf) out previous))) :
    Nonempty (Derivation positive Delta (graph2 (iterate leaf) out (suc count) state)) :=
  repeatSuccValue (transition leaf) count previous out state hr hl

theorem iterateCompose (leaf : Program 2) (first second state middle out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph2 (iterate leaf) middle first state)))
    (hs : Nonempty (Derivation positive Delta (graph2 (iterate leaf) out second middle))) :
    Nonempty (Derivation positive Delta (graph2 (iterate leaf) out (add first second) state)) :=
  fusionValue (transition leaf) first second state middle out hf hs

theorem iteratePadding (leaf : Program 2) (count budget state out stack : OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count budget)))
    (he : Nonempty (Derivation positive Delta (graph1 emptyState out stack)))
    (hr : Nonempty (Derivation positive Delta (graph2 (iterate leaf) out count state))) :
    Nonempty (Derivation positive Delta (graph2 (iterate leaf) out budget state)) := by
  apply weakGapCases count budget _ hb
  intro beta j Theta spare hj hsum
  rw [graph2Rename]
  have he' := renameInto he j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at he'
  rw [graph2Rename] at hr'
  exact headTransport (iterate leaf) (out.relabel j)
    (add (count.relabel j) spare) (budget.relabel j) (Fin.cons (state.relabel j) Fin.elim0) hsum
    (iterateCompose leaf (count.relabel j) spare (state.relabel j) (out.relabel j) (out.relabel j)
      hr' (iterateEmpty leaf spare (out.relabel j) (stack.relabel j) he'))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalIterationProof
