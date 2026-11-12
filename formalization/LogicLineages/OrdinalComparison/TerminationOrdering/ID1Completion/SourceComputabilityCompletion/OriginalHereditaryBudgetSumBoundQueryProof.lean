module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundQueryProof
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

open InternalApplicationCertificateConstructorsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel)
open InternalListCodecSupportProof (consGraphRename)
open OriginalHereditaryBudgetSumBoundCoreProof

theorem atCons (count jobs branching cap total head tail : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) jobs branching cap total)))
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail))) :
 Nonempty (Derivation body Delta (result (suc count) cap total)) := by
 let qs : Fin 2 → Program 3 := ![
   .composition OriginalHereditaryBudgetSum.jobBudget ![.projection 0,.projection 2],
   .composition OriginalHereditaryBudgetSum.sum ![.projection 1,.projection 2] ]
 let xs : Fin 3 → OTerm alpha := Fin.cons head (Fin.cons tail (Fin.cons branching Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 let xx : Fin 3 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (tail.relabel j) (Fin.cons (branching.relabel j) Fin.elim0))
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hq
 have hh := binaryRecover OriginalHereditaryBudgetSum.jobBudget (.projection 0) (.projection 2)
   (ys 0) (head.relabel j) (branching.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 2 xx)
 have ht := binaryRecover OriginalHereditaryBudgetSum.sum (.projection 1) (.projection 2)
   (ys 1) (tail.relabel j) (branching.relabel j) xx (hq 1) (projectionValue 1 xx) (projectionValue 2 xx)
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 have hc' := renameInto hc j Theta hj
 rw [consGraphRename] at hc'
 simp only [resultRename,sucRelabel]
 exact consCore (count.relabel j) (jobs.relabel j) (branching.relabel j) (cap.relabel j)
   (total.relabel j) (head.relabel j) (tail.relabel j) (ys 0) (ys 1) hi' hf' hc'
   (OriginalContextInsertionSupportProof.successorLengthTail _ _ _ _ hc' (InternalApplicationStepPeelSupportProof.andLeft hf')) hh ht

theorem succCore (count jobs branching cap total : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) jobs branching cap total))) :
 Nonempty (Derivation body Delta (result (suc count) cap total)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases jobs _
   (OriginalContextInsertionSupportProof.successorLengthNonzero count jobs (InternalApplicationStepPeelSupportProof.andLeft hf))
 intro beta j Theta head tail hj hc
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 simp only [resultRename,sucRelabel]
 exact atCons (count.relabel j) (jobs.relabel j) (branching.relabel j) (cap.relabel j)
   (total.relabel j) head tail hi' hf' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundQueryProof
