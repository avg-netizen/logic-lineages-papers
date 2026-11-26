module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableRootsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTagRecoverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableSharedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem actualShared (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out right parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 0) left))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 let q0 : Program 4 := rightOf (.projection 3)
 let q1 : Program 4 := leftOf q0
 let q2 : Program 4 := leftOf q1
 let q3 : Program 4 := .composition OriginalRootObservation.tag ![.projection 1,.projection 2]
 let q4 : Program 4 := leftOf (.projection 0)
 let q5 : Program 4 := rightOf (.projection 0)
 let qs : Fin 6 → Program 4 := ![q0,q1,q2,q3,q4,q5]
 let xs : Fin 4 → OTerm alpha := ![left,right,parameter,out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![left.relabel j,right.relabel j,parameter.relabel j,out.relabel j] : Fin 4 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 rw [hx] at hq
 let xx : Fin 4 → OTerm beta := ![left.relabel j,right.relabel j,parameter.relabel j,out.relabel j]
 have hi := unaryRecover InternalUnpair.right (.projection 3) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 3 xx)
 have hr := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have ho := unaryRecover InternalUnpair.left q1 (ys 2) (ys 1) xx (hq 2) (hq 1)
 have hrt := binaryRecover OriginalRootObservation.tag (.projection 1) (.projection 2) (ys 3)
   (right.relabel j) (parameter.relabel j) xx (hq 3) (projectionValue 1 xx) (projectionValue 2 xx)
 have hly := unaryRecover InternalUnpair.left (.projection 0) (ys 4) (left.relabel j) xx (hq 4) (projectionValue 0 xx)
 have hlr := unaryRecover InternalUnpair.right (.projection 0) (ys 5) (left.relabel j) xx (hq 5) (projectionValue 0 xx)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' hvl' hvr' ht'
 have hlt := RankCalibrationBaseTagProof.liftTag (left.relabel j) (parameter.relabel j) (ys 4) (ys 5) (numeral 0)
   (reconstructPair (left.relabel j) (ys 4) (ys 5) hly hlr) ht'
 have rootl := Context.EvaluatorChildrenProjectionProof.recursiveRoot R H G M W
   (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsl' hvl' hi hr
 have rootr := Context.EvaluatorChildrenProjectionProof.recursiveRoot R H G M W
   (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsr' hvr' hi hr
 have he0 := Context.EvaluatorAlignmentBranchesProof.tag0 (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   (left.relabel j) (parameter.relabel j) (ys 1) (ys 2) hlt rootl ho
 have her := Context.EvaluatorAlignmentTagRecoverProof.sourceTag (OriginalHereditaryEvaluatorDefinitions.evaluator R) H G M W
   (right.relabel j) (parameter.relabel j) (ys 3) (ys 1) (ys 2) hsr' hrt rootr ho
 simp only [equalEqn] at he0 her
 obtain ⟨he0⟩ := he0
 obtain ⟨her⟩ := her
 have hrt0 := outputTransport OriginalRootObservation.tag (ys 3) (numeral 0)
   (![right.relabel j,parameter.relabel j]) ⟨InternalTagArithmeticSupportProof.trans her he0⟩ hrt
 have he := EvaluatorOtherMarksVariableRootsProof.actualRoots (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   (left.relabel j) (right.relabel j) (parameter.relabel j) (ys 1) hlt hrt0 rootl rootr
 simpa only [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel] using he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableSharedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableSharedProof
