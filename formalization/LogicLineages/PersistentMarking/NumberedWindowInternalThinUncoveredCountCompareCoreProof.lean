module
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountMemberProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareStepProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareCoreProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open FirstOrder FirstOrder.Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus (Formula Derivation instantiate weaken)
open ID1Completion.InternalControlGraph
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
open NumberedWindowInternalThinUncoveredCount
open NumberedWindowInternalScratchInclusionThinProof (included includedRename includedSubst)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

open NumberedWindowInternalThinUncoveredCountCompareDefinitions.Compare NumberedWindowInternalThinUncoveredCountCompareSyntaxProof NumberedWindowInternalThinUncoveredCountCompareBindingProof NumberedWindowInternalThinUncoveredCountCompareStepProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consWithLeft (raw head tail left right leftCount rightCount candidate a : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta (graph2 count leftCount raw left)))
    (hr : Nonempty (Derivation body Delta (graph2 count rightCount raw right)))
    (ha : Nonempty (Derivation body Delta (graph2 count a tail left)))
    : Nonempty (Derivation body Delta (result raw left right leftCount rightCount candidate)) := by
  apply programCases count (Fin.cons tail (Fin.cons right Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hv
  have hrow' := renameInto hrow j Theta hj
  rw [belowRawRename] at hrow'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hi' := renameInto hi j Theta hj
  rw [includedRename] at hi'
  have hl' := renameInto hl j Theta hj
  rw [graph2Rename] at hl'
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  exact consKnown (raw.relabel j) (head.relabel j) (tail.relabel j) (left.relabel j) (right.relabel j) (leftCount.relabel j) (rightCount.relabel j) (candidate.relabel j) (a.relabel j) value hrow' hc' hi' hl' hr' ha' hv

theorem consCore (raw head tail left right leftCount rightCount candidate : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta (graph2 count leftCount raw left)))
    (hr : Nonempty (Derivation body Delta (graph2 count rightCount raw right)))
    : Nonempty (Derivation body Delta (result raw left right leftCount rightCount candidate)) := by
  apply programCases count (Fin.cons tail (Fin.cons left Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hv
  have hrow' := renameInto hrow j Theta hj
  rw [belowRawRename] at hrow'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hi' := renameInto hi j Theta hj
  rw [includedRename] at hi'
  have hl' := renameInto hl j Theta hj
  rw [graph2Rename] at hl'
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  exact consWithLeft (raw.relabel j) (head.relabel j) (tail.relabel j) (left.relabel j) (right.relabel j) (leftCount.relabel j) (rightCount.relabel j) (candidate.relabel j) value hrow' hc' hi' hl' hr' hv

theorem zeroCore (raw left right leftCount rightCount candidate : OrdinaryArithmetic.Term alpha)
    (hz : Nonempty (Derivation body Delta (eqn raw z)))
    (hl : Nonempty (Derivation body Delta (graph2 count leftCount raw left)))
    (hr : Nonempty (Derivation body Delta (graph2 count rightCount raw right))) :
    Nonempty (Derivation body Delta (result raw left right leftCount rightCount candidate)) := by
  have hl0 := headTransport count leftCount raw z (Fin.cons left Fin.elim0) hz hl
  have hr0 := headTransport count rightCount raw z (Fin.cons right Fin.elim0) hz hr
  obtain ⟨el⟩ := valueUnique count leftCount z ![z,left] hl0 (NumberedWindowInternalThinUncoveredCountStepProof.nilValue left)
  obtain ⟨er⟩ := valueUnique count rightCount z ![z,right] hr0 (NumberedWindowInternalThinUncoveredCountStepProof.nilValue right)
  let N := newness raw left right candidate
  have hp : Nonempty (Derivation body (N :: Delta) (graph2 scratchMember (suc z) raw candidate)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have hp0 := headTransport scratchMember (suc z) raw z (Fin.cons candidate Fin.elim0) (withHyp hz N) hp
  obtain ⟨hu⟩ := valueUnique scratchMember (suc z) z ![z,candidate] hp0
    (NumberedWindowInternalThinUncoveredCountMemberProof.memberNil candidate)
  exact ⟨Derivation.conjunctionIntroduction (orRight (trans er (symm el)))
    (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply hu)))⟩

theorem core (raw left right leftCount rightCount candidate : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta (graph2 count leftCount raw left)))
    (hr : Nonempty (Derivation body Delta (graph2 count rightCount raw right))) :
    Nonempty (Derivation body Delta (result raw left right leftCount rightCount candidate)) := by
  refine ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof.listCases raw
    (result raw left right leftCount rightCount candidate) ?_ ?_
  · exact zeroCore raw left right leftCount rightCount candidate ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hl (eqn raw z)) (withHyp hr (eqn raw z))
  · intro beta j Theta head tail hj hc
    rw [resultRename]
    have hrow' := renameInto hrow j Theta hj
    rw [belowRawRename] at hrow'
    have hi' := renameInto hi j Theta hj
    rw [includedRename] at hi'
    have hl' := renameInto hl j Theta hj
    rw [graph2Rename] at hl'
    have hr' := renameInto hr j Theta hj
    rw [graph2Rename] at hr'
    exact consCore (raw.relabel j) head tail (left.relabel j) (right.relabel j)
      (leftCount.relabel j) (rightCount.relabel j) (candidate.relabel j) hrow' hc hi' hl' hr'

end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareCoreProof
