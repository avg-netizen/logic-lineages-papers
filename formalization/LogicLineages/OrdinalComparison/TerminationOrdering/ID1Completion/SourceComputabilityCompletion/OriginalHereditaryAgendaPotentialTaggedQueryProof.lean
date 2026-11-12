module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftZero congAddLeft)
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalHereditaryAgendaPotentialTaggedSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalApplicationCertificateConstructorsSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open InternalListCodecSupportProof (consGraphRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaPotentialTaggedCoreProof

theorem atCons (count jobs tagged branching total head tail : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) jobs tagged branching total)))
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail))) :
 Nonempty (Derivation body Delta (result tagged branching total)) := by
 let qs : Fin 4 → Program 3 := ![
   pairOf (OriginalRawSyntaxTransport.constant 3 0) (.projection 0),
   .composition OriginalHereditaryVisitScheduler.tagVisits (fun _ : Fin 1 => .projection 1),
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
 have hv := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 0) (.projection 0)
   (ys 0) z (head.relabel j) xx (hq 0)
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx) (projectionValue 0 xx)
 have htag := unaryRecover OriginalHereditaryVisitScheduler.tagVisits (.projection 1) (ys 1) (tail.relabel j) xx (hq 1) (projectionValue 1 xx)
 have hh := binaryRecover OriginalHereditaryBudgetSum.jobBudget (.projection 0) (.projection 2)
   (ys 2) (head.relabel j) (branching.relabel j) xx (hq 2) (projectionValue 0 xx) (projectionValue 2 xx)
 have ht := binaryRecover OriginalHereditaryBudgetSum.sum (.projection 1) (.projection 2)
   (ys 3) (tail.relabel j) (branching.relabel j) xx (hq 3) (projectionValue 1 xx) (projectionValue 2 xx)
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 have hc' := renameInto hc j Theta hj
 rw [consGraphRename] at hc'
 rw [resultRename]
 exact consCore (count.relabel j) (jobs.relabel j) (tagged.relabel j) (branching.relabel j) (total.relabel j)
   (head.relabel j) (tail.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) hi' hf' hc'
   (OriginalContextInsertionSupportProof.successorLengthTail _ _ _ _ hc' (InternalApplicationStepPeelSupportProof.andLeft hf')) hv htag hh ht

theorem succCore (count jobs tagged branching total : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) jobs tagged branching total))) :
 Nonempty (Derivation body Delta (result tagged branching total)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases jobs _
   (OriginalContextInsertionSupportProof.successorLengthNonzero count jobs (InternalApplicationStepPeelSupportProof.andLeft hf))
 intro beta j Theta head tail hj hc
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 rw [resultRename]
 exact atCons (count.relabel j) (jobs.relabel j) (tagged.relabel j) (branching.relabel j) (total.relabel j)
   head tail hi' hf' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedQueryProof
