module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftZero associativity)
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalHereditaryAgendaPotentialAppendSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalApplicationCertificateConstructorsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel)
open InternalListCodecSupportProof (consGraphRename)
open OriginalHereditaryAgendaPotentialAppendCoreProof

theorem atCons (count front suffix joined branching a b head tail : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) front suffix joined branching a b)))
 (hc : Nonempty (Derivation body Delta (consGraph front head tail))) :
 Nonempty (Derivation body Delta (result joined branching a b)) := by
 let qs : Fin 3 → Program 4 := ![
   .composition InternalApplicationValidityStackAppend.append ![.projection 1,.projection 2],
   .composition OriginalHereditaryAgendaPotential.frameCost ![.projection 0,.projection 3],
   .composition OriginalHereditaryAgendaPotential.agenda ![.projection 1,.projection 3] ]
 let xs : Fin 4 → OTerm alpha := Fin.cons head (Fin.cons tail (Fin.cons suffix (Fin.cons branching Fin.elim0)))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 let xx : Fin 4 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (tail.relabel j) (Fin.cons (suffix.relabel j) (Fin.cons (branching.relabel j) Fin.elim0)))
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 rw [hx] at hq
 have happ := binaryRecover InternalApplicationValidityStackAppend.append (.projection 1) (.projection 2)
   (ys 0) (tail.relabel j) (suffix.relabel j) xx (hq 0) (projectionValue 1 xx) (projectionValue 2 xx)
 have hh := binaryRecover OriginalHereditaryAgendaPotential.frameCost (.projection 0) (.projection 3)
   (ys 1) (head.relabel j) (branching.relabel j) xx (hq 1) (projectionValue 0 xx) (projectionValue 3 xx)
 have ht := binaryRecover OriginalHereditaryAgendaPotential.agenda (.projection 1) (.projection 3)
   (ys 2) (tail.relabel j) (branching.relabel j) xx (hq 2) (projectionValue 1 xx) (projectionValue 3 xx)
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 have hc' := renameInto hc j Theta hj
 rw [consGraphRename] at hc'
 rw [resultRename]
 exact consCore (count.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j) (branching.relabel j)
   (a.relabel j) (b.relabel j) (head.relabel j) (tail.relabel j) (ys 0) (ys 1) (ys 2) hi' hf' hc'
   (OriginalContextInsertionSupportProof.successorLengthTail _ _ _ _ hc' (InternalApplicationStepPeelSupportProof.andLeft hf')) happ hh ht

theorem succCore (count front suffix joined branching a b : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) front suffix joined branching a b))) :
 Nonempty (Derivation body Delta (result joined branching a b)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases front _
   (OriginalContextInsertionSupportProof.successorLengthNonzero count front (InternalApplicationStepPeelSupportProof.andLeft hf))
 intro beta j Theta head tail hj hc
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 rw [resultRename]
 exact atCons (count.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j) (branching.relabel j)
   (a.relabel j) (b.relabel j) head tail hi' hf' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendQueryProof
