module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.BoundBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.BoundCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open BoundDefinitions.Bound BoundSyntaxProof BoundBindingProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open InternalListCodecDecompositionSupportProof
open OrderProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consKnown (raw head tail reached remaining size tailCount tailSize : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ho : Nonempty (Derivation body Delta (graph2 count remaining raw reached)))
    (hl : Nonempty (Derivation body Delta (lengthGraph size raw)))
    (ht : Nonempty (Derivation body Delta (graph2 count tailCount tail reached)))
    (hs : Nonempty (Derivation body Delta (lengthGraph tailSize tail))) :
    Nonempty (Derivation body Delta (result raw reached remaining size)) := by
  have hi := belowRawApply raw tail reached tailCount tailSize hb
    (consTailDescent raw head tail hc) (andIntro ht hs)
  have heSize := lengthConsRecover raw head tail size tailSize hc hl hs
  obtain ⟨heSize⟩ := heSize
  let A := graph2 contains (suc z) reached head
  apply formulaCases A
  · obtain ⟨he⟩ := StepProof.consHitEquation raw head tail reached remaining tailCount
      (withHyp hc A) (withHyp ht A) (withHyp ho A) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact OrderProof.transport tailCount (suc tailSize) remaining size ⟨symm he⟩
      ⟨symm (addHyp heSize A)⟩ (OrderProof.rightSuccessorBound tailCount tailSize (withHyp hi A))
  · obtain ⟨he⟩ := StepProof.consMissEquation raw head tail reached remaining tailCount
      (withHyp hc A.not) (withHyp ht A.not) (withHyp ho A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact OrderProof.transport (suc tailCount) (suc tailSize) remaining size ⟨symm he⟩
      ⟨symm (addHyp heSize A.not)⟩ (OrderProof.successor tailCount tailSize (withHyp hi A.not))

theorem consWithCount (raw head tail reached remaining size tailCount : OTerm alpha)
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

theorem consCore (raw head tail reached remaining size : OTerm alpha)
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

theorem zeroCore (raw reached remaining size : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (eqn raw z)))
    (ho : Nonempty (Derivation body Delta (graph2 count remaining raw reached)))
    (hl : Nonempty (Derivation body Delta (lengthGraph size raw))) :
    Nonempty (Derivation body Delta (result raw reached remaining size)) := by
  have ho0 := headTransport count remaining raw z (Fin.cons reached Fin.elim0) hz ho
  have hl0 := headTransport length size raw z Fin.elim0 hz hl
  obtain ⟨hc⟩ := valueUnique count remaining z ![z,reached] ho0 (StepProof.nilValue reached)
  obtain ⟨hs⟩ := lengthNilRecover size hl0
  exact ⟨orRight (trans hc (symm hs))⟩

theorem core (raw reached remaining size : OTerm alpha)
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.BoundCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.BoundCoreProof
