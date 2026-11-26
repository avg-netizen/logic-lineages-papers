module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalNumericListSort OriginalNumericListSortPrefixDefinitions OriginalNumericListSortPrefixSyntaxProof
open OriginalNumericListSortPrefixBindingProof OriginalNumericListSortAdjacentSupportProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] sort OriginalNumericListSort.insert

theorem atZero (raw tailA tailB left right a b outA outB : OTerm alpha)
 (hz : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields raw tailA tailB left right a b outA outB))) :
 Nonempty (Derivation body Delta (equal outA outB)) := by
 have hla := headTransport InternalApplicationValidityStackAppend.append left raw z (Fin.cons tailA Fin.elim0) hz (andLeft hf)
 have hra := headTransport InternalApplicationValidityStackAppend.append right raw z (Fin.cons tailB Fin.elim0) hz (andLeft (andRight hf))
 have hl := InternalApplicationValidityStackAppendListProof.appendZeroRecover left tailA hla
 have hr := InternalApplicationValidityStackAppendListProof.appendZeroRecover right tailB hra
 have hsl := headTransport sort outA left tailA Fin.elim0 hl (andLeft (andRight (andRight (andRight (andRight (andRight hf))))))
 have hsr := headTransport sort outB right tailB Fin.elim0 hr (andRight (andRight (andRight (andRight (andRight (andRight hf))))))
 obtain ⟨he1⟩ := valueUnique sort outA a (Fin.cons tailA Fin.elim0) hsl (andLeft (andRight (andRight hf)))
 obtain ⟨he2⟩ := valueUnique sort b outB (Fin.cons tailB Fin.elim0) (andLeft (andRight (andRight (andRight hf)))) hsr
 obtain ⟨he⟩ := (andLeft (andRight (andRight (andRight (andRight hf)))))
 simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.trans he1
   (InternalTagArithmeticSupportProof.trans (by simpa only [equalEqn] using he) he2)))

theorem atCons (raw tailA tailB left right a b outA outB head rest : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head rest)))
 (hf : Nonempty (Derivation body Delta (fields raw tailA tailB left right a b outA outB))) :
 Nonempty (Derivation body Delta (equal outA outB)) := by
 apply binaryCases InternalApplicationValidityStackAppend.append rest tailA _
 intro beta1 j1 Theta1 childLeft hj1 hchildLeft
 rw [equalRename]
 have hi_1 := renameInto hi j1 Theta1 hj1
 simp only [belowRawRename] at hi_1
 have hc_1 := renameInto hc j1 Theta1 hj1
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hc_1
 have hf_1 := renameInto hf j1 Theta1 hj1
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hf_1
 apply binaryCases InternalApplicationValidityStackAppend.append (rest.relabel j1) (tailB.relabel j1) _
 intro beta2 j2 Theta2 childRight hj2 hchildRight
 rw [equalRename]
 have hi_2 := renameInto hi_1 j2 Theta2 hj2
 simp only [belowRawRename] at hi_2
 have hc_2 := renameInto hc_1 j2 Theta2 hj2
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hc_2
 have hf_2 := renameInto hf_1 j2 Theta2 hj2
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hf_2
 have hchildLeft_2 := renameInto hchildLeft j2 Theta2 hj2
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hchildLeft_2
 apply unaryCases sort (childLeft.relabel j2) _
 intro beta3 j3 Theta3 sortedLeft hj3 hsortedLeft
 rw [equalRename]
 have hi_3 := renameInto hi_2 j3 Theta3 hj3
 simp only [belowRawRename] at hi_3
 have hc_3 := renameInto hc_2 j3 Theta3 hj3
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hc_3
 have hf_3 := renameInto hf_2 j3 Theta3 hj3
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hf_3
 have hchildLeft_3 := renameInto hchildLeft_2 j3 Theta3 hj3
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hchildLeft_3
 have hchildRight_3 := renameInto hchildRight j3 Theta3 hj3
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hchildRight_3
 apply unaryCases sort (childRight.relabel j3) _
 intro beta4 j4 Theta4 sortedRight hj4 hsortedRight
 rw [equalRename]
 have hi_4 := renameInto hi_3 j4 Theta4 hj4
 simp only [belowRawRename] at hi_4
 have hc_4 := renameInto hc_3 j4 Theta4 hj4
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hc_4
 have hf_4 := renameInto hf_3 j4 Theta4 hj4
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hf_4
 have hchildLeft_4 := renameInto hchildLeft_3 j4 Theta4 hj4
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hchildLeft_4
 have hchildRight_4 := renameInto hchildRight_3 j4 Theta4 hj4
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hchildRight_4
 have hsortedLeft_4 := renameInto hsortedLeft j4 Theta4 hj4
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hsortedLeft_4
 have hleft := InternalApplicationValidityStackAppendListProof.consForward ((((raw.relabel j1).relabel j2).relabel j3).relabel j4) ((((head.relabel j1).relabel j2).relabel j3).relabel j4) ((((rest.relabel j1).relabel j2).relabel j3).relabel j4) ((((tailA.relabel j1).relabel j2).relabel j3).relabel j4) (((childLeft.relabel j2).relabel j3).relabel j4) ((((left.relabel j1).relabel j2).relabel j3).relabel j4) hc_4 hchildLeft_4 (andLeft hf_4)
 have hright := InternalApplicationValidityStackAppendListProof.consForward ((((raw.relabel j1).relabel j2).relabel j3).relabel j4) ((((head.relabel j1).relabel j2).relabel j3).relabel j4) ((((rest.relabel j1).relabel j2).relabel j3).relabel j4) ((((tailB.relabel j1).relabel j2).relabel j3).relabel j4) ((childRight.relabel j3).relabel j4) ((((right.relabel j1).relabel j2).relabel j3).relabel j4) hc_4 hchildRight_4 (andLeft (andRight hf_4))
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent ((((raw.relabel j1).relabel j2).relabel j3).relabel j4) ((((head.relabel j1).relabel j2).relabel j3).relabel j4) ((((rest.relabel j1).relabel j2).relabel j3).relabel j4) hc_4
 have he := belowRawApply ((((raw.relabel j1).relabel j2).relabel j3).relabel j4) ((((rest.relabel j1).relabel j2).relabel j3).relabel j4) ((((tailA.relabel j1).relabel j2).relabel j3).relabel j4) ((((tailB.relabel j1).relabel j2).relabel j3).relabel j4) (((childLeft.relabel j2).relabel j3).relabel j4) ((childRight.relabel j3).relabel j4) ((((a.relabel j1).relabel j2).relabel j3).relabel j4) ((((b.relabel j1).relabel j2).relabel j3).relabel j4) (sortedLeft.relabel j4) sortedRight hi_4 hb
   (andIntro hchildLeft_4 (andIntro hchildRight_4 (andIntro (andLeft (andRight (andRight hf_4))) (andIntro (andLeft (andRight (andRight (andRight hf_4)))) (andIntro (andLeft (andRight (andRight (andRight (andRight hf_4))))) (andIntro hsortedLeft_4 hsortedRight))))))
 have hil := sortConsRecover ((((left.relabel j1).relabel j2).relabel j3).relabel j4) ((((head.relabel j1).relabel j2).relabel j3).relabel j4) (((childLeft.relabel j2).relabel j3).relabel j4) (sortedLeft.relabel j4) ((((outA.relabel j1).relabel j2).relabel j3).relabel j4) hleft hsortedLeft_4 (andLeft (andRight (andRight (andRight (andRight (andRight hf_4))))))
 have hir := sortConsRecover ((((right.relabel j1).relabel j2).relabel j3).relabel j4) ((((head.relabel j1).relabel j2).relabel j3).relabel j4) ((childRight.relabel j3).relabel j4) sortedRight ((((outB.relabel j1).relabel j2).relabel j3).relabel j4) hright hsortedRight (andRight (andRight (andRight (andRight (andRight (andRight hf_4))))))
 obtain ⟨he⟩ := he
 have heq : Nonempty (Derivation body Theta4 (eqn sortedRight (sortedLeft.relabel j4))) :=
   ⟨InternalTagArithmeticSupportProof.symm (by simpa only [equalEqn] using he)⟩
 have hir' := headTransport OriginalNumericListSort.insert ((((outB.relabel j1).relabel j2).relabel j3).relabel j4) sortedRight (sortedLeft.relabel j4) (Fin.cons ((((head.relabel j1).relabel j2).relabel j3).relabel j4) Fin.elim0) heq hir
 simpa only [equalEqn] using valueUnique OriginalNumericListSort.insert ((((outA.relabel j1).relabel j2).relabel j3).relabel j4) ((((outB.relabel j1).relabel j2).relabel j3).relabel j4)
   (Fin.cons (sortedLeft.relabel j4) (Fin.cons ((((head.relabel j1).relabel j2).relabel j3).relabel j4) Fin.elim0)) hil hir'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixCoreProof
