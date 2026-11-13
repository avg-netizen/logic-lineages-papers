module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableRootsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem actualRoots (R : Program 2) (left right parameter root : OTerm alpha)
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 0) left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 0) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root right parameter))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 let q0 : Program 3 := rightOf (.projection 0)
 let q1 : Program 3 := rightOf (.projection 1)
 let q2 : Program 3 := rightOf (.projection 2)
 let q3 : Program 3 := leftOf q2
 let q4 : Program 3 := rightOf q2
 let qs : Fin 5 → Program 3 := ![q0,q1,q2,q3,q4]
 let xs : Fin 3 → OTerm alpha := ![left,right,root]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![left.relabel j,right.relabel j,root.relabel j] : Fin 3 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hq
 let xx : Fin 3 → OTerm beta := ![left.relabel j,right.relabel j,root.relabel j]
 have hlraw := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (left.relabel j) xx (hq 0) (projectionValue 0 xx)
 have hrraw := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (right.relabel j) xx (hq 1) (projectionValue 1 xx)
 have hd := unaryRecover InternalUnpair.right (.projection 2) (ys 2) (root.relabel j) xx (hq 2) (projectionValue 2 xx)
 have hy := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have hi := unaryRecover InternalUnpair.right q2 (ys 4) (ys 2) xx (hq 4) (hq 2)
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at htl' htr' hvl' hvr'
 have hl := EvaluatorOtherMarksVariableCodecProof.actualRepack R (left.relabel j) (parameter.relabel j)
   (root.relabel j) (ys 0) (ys 2) (ys 3) (ys 4) htl' hvl' hlraw hd hy hi
 have hr := EvaluatorOtherMarksVariableCodecProof.actualRepack R (right.relabel j) (parameter.relabel j)
   (root.relabel j) (ys 1) (ys 2) (ys 3) (ys 4) htr' hvr' hrraw hd hy hi
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 exact valueUnique EvaluatorOtherMarksVariableCodecProof.repack (left.relabel j) (right.relabel j)
   (Fin.cons (root.relabel j) Fin.elim0) hl hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableRootsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableRootsProof
