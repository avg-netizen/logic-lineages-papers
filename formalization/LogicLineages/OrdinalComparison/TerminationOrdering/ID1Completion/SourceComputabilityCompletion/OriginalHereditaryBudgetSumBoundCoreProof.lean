module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalListCodecSupportProof (consGraph)
open InternalMultiplicationLawsProof (mul multiplicationLeftZero)
open InternalAdditionLawsProof (add)
open InternalOriginalPairingOrderArithmeticProof (weakTransport addWeakBoth)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalHereditaryBudgetSumBound OriginalHereditaryBudgetSumBoundSyntaxProof
open OriginalHereditaryBudgetSumBoundCellsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (jobs branching cap total : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z jobs branching cap total))) :
 Nonempty (Derivation body Delta (result z cap total)) := by
 have hj := lengthZeroRecover jobs (InternalApplicationStepPeelSupportProof.andLeft hf)
 have hs := headTransport OriginalHereditaryBudgetSum.sum total jobs z (Fin.cons branching Fin.elim0) hj (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))
 have he := valueUnique OriginalHereditaryBudgetSum.sum total z (Fin.cons z (Fin.cons branching Fin.elim0)) hs
   (OriginalHereditaryBudgetSumRecurrenceProof.nilValue branching)
 exact weakTransport total (mul z cap) z z he ⟨multiplicationLeftZero cap⟩
   ⟨InternalQuotientComparisonProof.equalToNext (refl z)⟩

theorem consCore (count jobs branching cap total head tail headValue tailValue : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) jobs branching cap total)))
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count tail)))
 (hh : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.jobBudget headValue head branching)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum tailValue tail branching))) :
 Nonempty (Derivation body Delta (result (suc count) cap total)) := by
 have hhead := headBound count jobs head tail branching cap headValue hc (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf)) hh
 have htail := rowApply count tail branching cap tailValue hi
   (InternalApplicationStepPeelSupportProof.andIntro hl (InternalApplicationStepPeelSupportProof.andIntro (tailBound count jobs head tail branching cap hc (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf))) ht))
 have he := OriginalHereditaryBudgetSumRecurrenceProof.consEquation jobs head tail branching headValue tailValue total
   hc hh ht (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))
 have hm : Nonempty (Derivation body Delta (eqn (mul (suc count) cap) (add cap (mul count cap)))) :=
   ⟨trans (InternalMultiplicationLeftSuccessorProof.leftSuccessorMultiplication count cap)
     (InternalAdditionLawsProof.commutativity (mul count cap) cap)⟩
 exact weakTransport total (mul (suc count) cap) (add headValue tailValue) (add cap (mul count cap))
   he hm (addWeakBoth headValue cap tailValue (mul count cap) hhead htail)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCoreProof
