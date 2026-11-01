module
public import LogicLineages.OrdinalComparison.RangeRangeNodeTargets
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramProof
public import LogicLineages.OrdinalComparison.SuccessorWordProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem limit_fixed : Targets.ActualSuccessorNormalizationLimitFixed := by
  intro w E eta lower c hl
  have hrem : encodedOrdinalFiniteRemainder (rawNoteEncode eta.1)=0 :=
    (OrdinalSuccessorProgram.classification eta).mpr (Or.inr hl)
  let source := oneVariableComparisonEncode (.range w E)
  let s := encodedSuccessorNormalizationInitial source (rawNoteEncode eta.1) c
  have hactive : ¬encodedSuccessorNormalizationActive (rawNoteEncode lower.1) s := by
    change ¬(rawComparisonCode _ _=2 ∧ 0<encodedOrdinalFiniteRemainder (rawNoteEncode eta.1))
    rw [hrem]
    omega
  have hfixed : encodedSuccessorNormalizationStep (rawNoteEncode lower.1) c s=s := by
    rw [encodedSuccessorNormalizationStep,if_neg hactive]
  have htrace : encodedSuccessorNormalizationTrace source (rawNoteEncode eta.1) (rawNoteEncode lower.1) c
      (rawNormCode (rawNoteEncode eta.1))=s := Function.iterate_fixed hfixed _
  change (encodedComparisonAppendKernel
    (encodedSuccessorNormalizationTrace source (rawNoteEncode eta.1) (rawNoteEncode lower.1) c
      (rawNormCode (rawNoteEncode eta.1))).1
    (encodedSuccessorNormalizationTrace source (rawNoteEncode eta.1) (rawNoteEncode lower.1) c
      (rawNormCode (rawNoteEncode eta.1))).2.1 c,
    (encodedSuccessorNormalizationTrace source (rawNoteEncode eta.1) (rawNoteEncode lower.1) c
      (rawNormCode (rawNoteEncode eta.1))).2.1,
    (encodedSuccessorNormalizationTrace source (rawNoteEncode eta.1) (rawNoteEncode lower.1) c
      (rawNormCode (rawNoteEncode eta.1))).2.2)=_
  rw [htrace]
  simp only [s,source,encodedSuccessorNormalizationInitial,(SuccessorWordProgram.source w E eta eta c).1]

end LogicLineages.OrdinalComparison.RangeRangeNode
