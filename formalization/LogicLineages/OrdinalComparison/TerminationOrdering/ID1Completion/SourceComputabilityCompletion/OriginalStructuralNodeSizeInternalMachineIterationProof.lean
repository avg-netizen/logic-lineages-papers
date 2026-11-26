module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineEmptyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationResultStack (emptyState)
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

theorem iterateEmpty (count state stack : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph1 emptyState state stack))) :
    Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) state count state)) :=
  fixedValue (OriginalStructuralNodeSize.transition) count state
    (OriginalStructuralNodeSizeInternalMachineEmptyProof.emptyFixed stack state hs)

theorem iterateOne (state out : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state))) :
    Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) out (suc z) state)) :=
  repeatSuccValue (OriginalStructuralNodeSize.transition) z state out state (repeatZeroValue (OriginalStructuralNodeSize.transition) state) h

theorem iterateAfterFirst (count state next out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) next state)))
    (hr : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) out count next))) :
    Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) out (suc count) state)) := by
  have hsum := fusionValue (OriginalStructuralNodeSize.transition) (suc z) count state next out (iterateOne state next hf) hr
  have he : Derivation positive Delta (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  exact headTransport (OriginalStructuralNodeSize.iterate) out (add (suc z) count) (suc count)
    (Fin.cons state Fin.elim0) ⟨he⟩ hsum

theorem iterateAfterLast (count state previous out : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) previous count state)))
    (hl : Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out previous))) :
    Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) out (suc count) state)) :=
  repeatSuccValue (OriginalStructuralNodeSize.transition) count previous out state hr hl

theorem iterateCompose (first second state middle out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) middle first state)))
    (hs : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) out second middle))) :
    Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) out (add first second) state)) :=
  fusionValue (OriginalStructuralNodeSize.transition) first second state middle out hf hs

theorem iteratePadding (count budget state out stack : OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count budget)))
    (he : Nonempty (Derivation positive Delta (graph1 emptyState out stack)))
    (hr : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) out count state))) :
    Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) out budget state)) := by
  apply weakGapCases count budget _ hb
  intro beta j Theta spare hj hsum
  rw [graph2Rename]
  have he' := renameInto he j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at he'
  rw [graph2Rename] at hr'
  exact headTransport (OriginalStructuralNodeSize.iterate) (out.relabel j)
    (add (count.relabel j) spare) (budget.relabel j) (Fin.cons (state.relabel j) Fin.elim0) hsum
    (iterateCompose (count.relabel j) spare (state.relabel j) (out.relabel j) (out.relabel j)
      hr' (iterateEmpty spare (out.relabel j) (stack.relabel j) he'))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineIterationProof
