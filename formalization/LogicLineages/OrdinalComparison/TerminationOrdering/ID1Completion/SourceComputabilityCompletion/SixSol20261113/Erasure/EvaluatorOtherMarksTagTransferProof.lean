module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTagTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Erasure.EvaluatorErasureDefinitions SixSol20261113.Erasure.EvaluatorErasureSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
/-- Original source/E equality transfers an actual packed tag graph. -/
theorem actualTagTransfer (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter label : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
 (ho : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag label left))) :
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag label right)) := by
 let qs : Fin 6 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1),
   leftOf (rightOf (.projection 0)),leftOf (rightOf (.projection 1)),
   leftOf (.projection 0),leftOf (.projection 1)]
 let xs : Fin 2 → OTerm alpha := ![left,right]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta values hj hg
 have hx : (fun i => (xs i).relabel j) = (![left.relabel j,right.relabel j] : Fin 2 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hg
 let xx : Fin 2 → OTerm beta := ![left.relabel j,right.relabel j]
 have hrl := unaryRecover InternalUnpair.right (.projection 0) (values 0) (left.relabel j) xx (hg 0) (projectionValue 0 xx)
 have hrr := unaryRecover InternalUnpair.right (.projection 1) (values 1) (right.relabel j) xx (hg 1) (projectionValue 1 xx)
 have htl := unaryRecover InternalUnpair.left (rightOf (.projection 0)) (values 2) (values 0) xx (hg 2) (hg 0)
 have htr := unaryRecover InternalUnpair.left (rightOf (.projection 1)) (values 3) (values 1) xx (hg 3) (hg 1)
 have hyl := unaryRecover InternalUnpair.left (.projection 0) (values 4) (left.relabel j) xx (hg 4) (projectionValue 0 xx)
 have hyr := unaryRecover InternalUnpair.left (.projection 1) (values 5) (right.relabel j) xx (hg 5) (projectionValue 1 xx)
 let lx : Fin 2 → OTerm beta := ![left.relabel j,parameter.relabel j]
 let rx : Fin 2 → OTerm beta := ![right.relabel j,parameter.relabel j]
 have gl : Nonempty (Derivation body Theta (graph2 OriginalRootObservation.tag (values 2) (left.relabel j) (parameter.relabel j))) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (values 2) (values 0) lx htl
     (unaryValue InternalUnpair.right (.projection 0) (values 0) (left.relabel j) lx hrl (projectionValue 0 lx))
 have gr : Nonempty (Derivation body Theta (graph2 OriginalRootObservation.tag (values 3) (right.relabel j) (parameter.relabel j))) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (values 3) (values 1) rx htr
     (unaryValue InternalUnpair.right (.projection 0) (values 1) (right.relabel j) rx hrr (projectionValue 0 rx))
 have ha' := renameInto ha j Theta hj
 rw [admittedRename] at ha'
 have ho' := renameInto ho j Theta hj
 simp only [graph1Rename,sucRelabel,zRelabel] at ho' ⊢
 have he := andLeft (Context.EvaluatorAlignmentProof.actualRoot R H G M W body beta Theta
   (left.relabel j) (right.relabel j) (parameter.relabel j) (values 2) (values 3) (values 4) (values 5)
   ha' (andIntro gl hyl) (andIntro gr hyr))
 have heq := (congrArg (fun f => Nonempty (Derivation body Theta f)) (equalEqn (values 2) (values 3))).mp he
 have htl' := outputTransport InternalUnpair.left (values 2) (values 3) ![values 0] heq htl
 let ls : Fin 1 → OTerm beta := ![left.relabel j]
 let rs : Fin 1 → OTerm beta := ![right.relabel j]
 have ul : Nonempty (Derivation body Theta (graph1 OriginalLambdaTraversal.rawTag (values 3) (left.relabel j))) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (values 3) (values 0) ls htl'
     (unaryValue InternalUnpair.right (.projection 0) (values 0) (left.relabel j) ls hrl (projectionValue 0 ls))
 have ur : Nonempty (Derivation body Theta (graph1 OriginalLambdaTraversal.rawTag (values 3) (right.relabel j))) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (values 3) (values 1) rs htr
     (unaryValue InternalUnpair.right (.projection 0) (values 1) (right.relabel j) rs hrr (projectionValue 0 rs))
 have et := valueUnique OriginalLambdaConstructor.tag (values 3) (label.relabel j)
   (Fin.cons (left.relabel j) Fin.elim0) ul ho'
 exact outputTransport OriginalLambdaConstructor.tag (values 3) (label.relabel j)
   (Fin.cons (right.relabel j) Fin.elim0) et ur
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTagTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTagTransferProof
