module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountStepProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundCoreProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open FirstOrder FirstOrder.Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculus (Derivation Formula)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraph (equal)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof
open LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion
open NumberedWindowInternalThinUncoveredCount
open NumberedWindowInternalThinUncoveredCountOrderProof
open NumberedWindowInternalSparseScratchMembership (scratchMember)

open NumberedWindowInternalThinUncoveredCountBoundDefinitions.Bound NumberedWindowInternalThinUncoveredCountBoundSyntaxProof NumberedWindowInternalThinUncoveredCountBoundBindingProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open NumberedWindowInternalThinUncoveredCountStepProof
open InternalListCodecDecompositionSupportProof
open NumberedWindowInternalThinUncoveredCountOrderProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consKnown (raw head tail reached remaining size tailCount tailSize : OrdinaryArithmetic.Term alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ho : Nonempty (Derivation body Delta (graph2 count remaining raw reached)))
    (hl : Nonempty (Derivation body Delta (lengthGraph size raw)))
    (ht : Nonempty (Derivation body Delta (graph2 count tailCount tail reached)))
    (hs : Nonempty (Derivation body Delta (lengthGraph tailSize tail))) :
    Nonempty (Derivation body Delta (result raw reached remaining size)) := by
  have hi := belowRawApply raw tail reached tailCount tailSize hb
    (consTailDescent raw head tail hc) (InternalApplicationStepPeelSupportProof.andIntro ht hs)
  have heSize := lengthConsRecover raw head tail size tailSize hc hl hs
  obtain ⟨heSize⟩ := heSize
  let A := graph2 scratchMember (suc z) reached head
  apply formulaCases A
  · obtain ⟨he⟩ := NumberedWindowInternalThinUncoveredCountStepProof.consHitEquation raw head tail reached remaining tailCount
      (withHyp hc A) (withHyp ht A) (withHyp ho A) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact NumberedWindowInternalThinUncoveredCountOrderProof.transport tailCount (suc tailSize) remaining size ⟨symm he⟩
      ⟨symm (addHyp heSize A)⟩ (NumberedWindowInternalThinUncoveredCountOrderProof.rightSuccessorBound tailCount tailSize (withHyp hi A))
  · obtain ⟨he⟩ := NumberedWindowInternalThinUncoveredCountStepProof.consMissEquation raw head tail reached remaining tailCount
      (withHyp hc A.not) (withHyp ht A.not) (withHyp ho A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact NumberedWindowInternalThinUncoveredCountOrderProof.transport (suc tailCount) (suc tailSize) remaining size ⟨symm he⟩
      ⟨symm (addHyp heSize A.not)⟩ (NumberedWindowInternalThinUncoveredCountOrderProof.successor tailCount tailSize (withHyp hi A.not))

theorem consWithCount (raw head tail reached remaining size tailCount : OrdinaryArithmetic.Term alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ho : Nonempty (Derivation body Delta (graph2 count remaining raw reached)))
    (hl : Nonempty (Derivation body Delta (lengthGraph size raw)))
    (ht : Nonempty (Derivation body Delta (graph2 count tailCount tail reached))) :
    Nonempty (Derivation body Delta (result raw reached remaining size)) := by
  apply programCases length (Fin.cons tail Fin.elim0) _
  intro beta j Theta tailSize hj hs
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hs
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have ho' := renameInto ho j Theta hj
  rw [graph2Rename] at ho'
  have hl' := renameInto hl j Theta hj
  rw [lengthRename] at hl'
  have ht' := renameInto ht j Theta hj
  rw [graph2Rename] at ht'
  exact consKnown (raw.relabel j) (head.relabel j) (tail.relabel j) (reached.relabel j)
    (remaining.relabel j) (size.relabel j) (tailCount.relabel j) tailSize hb' hc' ho' hl' ht' hs

theorem consCore (raw head tail reached remaining size : OrdinaryArithmetic.Term alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ho : Nonempty (Derivation body Delta (graph2 count remaining raw reached)))
    (hl : Nonempty (Derivation body Delta (lengthGraph size raw))) :
    Nonempty (Derivation body Delta (result raw reached remaining size)) := by
  apply programCases count (Fin.cons tail (Fin.cons reached Fin.elim0)) _
  intro beta j Theta tailCount hj ht
  rw [resultRename]
  simp only [consTermRename,emptyRename] at ht
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have ho' := renameInto ho j Theta hj
  rw [graph2Rename] at ho'
  have hl' := renameInto hl j Theta hj
  rw [lengthRename] at hl'
  exact consWithCount (raw.relabel j) (head.relabel j) (tail.relabel j) (reached.relabel j)
    (remaining.relabel j) (size.relabel j) tailCount hb' hc' ho' hl' ht

theorem zeroCore (raw reached remaining size : OrdinaryArithmetic.Term alpha)
    (hz : Nonempty (Derivation body Delta (eqn raw z)))
    (ho : Nonempty (Derivation body Delta (graph2 count remaining raw reached)))
    (hl : Nonempty (Derivation body Delta (lengthGraph size raw))) :
    Nonempty (Derivation body Delta (result raw reached remaining size)) := by
  have ho0 := headTransport count remaining raw z (Fin.cons reached Fin.elim0) hz ho
  have hl0 := headTransport length size raw z Fin.elim0 hz hl
  obtain ⟨hc⟩ := valueUnique count remaining z ![z,reached] ho0 (NumberedWindowInternalThinUncoveredCountStepProof.nilValue reached)
  obtain ⟨hs⟩ := lengthNilRecover size hl0
  exact ⟨orRight (trans hc (symm hs))⟩

theorem core (raw reached remaining size : OrdinaryArithmetic.Term alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (ho : Nonempty (Derivation body Delta (graph2 count remaining raw reached)))
    (hl : Nonempty (Derivation body Delta (lengthGraph size raw))) :
    Nonempty (Derivation body Delta (result raw reached remaining size)) := by
  apply listCases raw
  · exact zeroCore raw reached remaining size ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp ho (eqn raw z)) (withHyp hl (eqn raw z))
  · intro beta j Theta head tail hj hc
    rw [resultRename]
    have hb' := renameInto hb j Theta hj
    rw [belowRawRename] at hb'
    have ho' := renameInto ho j Theta hj
    rw [graph2Rename] at ho'
    have hl' := renameInto hl j Theta hj
    rw [lengthRename] at hl'
    exact consCore (raw.relabel j) head tail (reached.relabel j) (remaining.relabel j)
      (size.relabel j) hb' hc ho' hl'

end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundCoreProof
