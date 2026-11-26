module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineEmptyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineIterationProof
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

theorem iterateEmpty (mode : Mode) (count state stack : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph1 emptyState state stack))) :
    Nonempty (Derivation positive Delta (graph2 (iterate mode) state count state)) :=
  fixedValue (transition mode) count state
    (OriginalRawSyntaxTransportInternalMachineEmptyProof.emptyFixed mode stack state hs)

theorem iterateOne (mode : Mode) (state out : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph1 (transition mode) out state))) :
    Nonempty (Derivation positive Delta (graph2 (iterate mode) out (suc z) state)) :=
  repeatSuccValue (transition mode) z state out state (repeatZeroValue (transition mode) state) h

theorem iterateAfterFirst (mode : Mode) (count state next out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph1 (transition mode) next state)))
    (hr : Nonempty (Derivation positive Delta (graph2 (iterate mode) out count next))) :
    Nonempty (Derivation positive Delta (graph2 (iterate mode) out (suc count) state)) := by
  have hsum := fusionValue (transition mode) (suc z) count state next out (iterateOne mode state next hf) hr
  have he : Derivation positive Delta (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  exact headTransport (iterate mode) out (add (suc z) count) (suc count)
    (Fin.cons state Fin.elim0) ⟨he⟩ hsum

theorem iterateAfterLast (mode : Mode) (count state previous out : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph2 (iterate mode) previous count state)))
    (hl : Nonempty (Derivation positive Delta (graph1 (transition mode) out previous))) :
    Nonempty (Derivation positive Delta (graph2 (iterate mode) out (suc count) state)) :=
  repeatSuccValue (transition mode) count previous out state hr hl

theorem iterateCompose (mode : Mode) (first second state middle out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph2 (iterate mode) middle first state)))
    (hs : Nonempty (Derivation positive Delta (graph2 (iterate mode) out second middle))) :
    Nonempty (Derivation positive Delta (graph2 (iterate mode) out (add first second) state)) :=
  fusionValue (transition mode) first second state middle out hf hs

theorem iteratePadding (mode : Mode) (count budget state out stack : OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count budget)))
    (he : Nonempty (Derivation positive Delta (graph1 emptyState out stack)))
    (hr : Nonempty (Derivation positive Delta (graph2 (iterate mode) out count state))) :
    Nonempty (Derivation positive Delta (graph2 (iterate mode) out budget state)) := by
  apply weakGapCases count budget _ hb
  intro beta j Theta spare hj hsum
  rw [graph2Rename]
  have he' := renameInto he j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at he'
  rw [graph2Rename] at hr'
  exact headTransport (iterate mode) (out.relabel j)
    (add (count.relabel j) spare) (budget.relabel j) (Fin.cons (state.relabel j) Fin.elim0) hsum
    (iterateCompose mode (count.relabel j) spare (state.relabel j) (out.relabel j) (out.relabel j)
      hr' (iterateEmpty mode spare (out.relabel j) (stack.relabel j) he'))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineIterationProof
