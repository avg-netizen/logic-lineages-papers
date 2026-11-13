module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenInverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTagRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTypeDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentRootSharedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorChildrenInverseProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open SixSol20261113.Erasure.EvaluatorErasureSyntax

theorem root (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out ltg rtg lty rty : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag ltg left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag rtg right parameter)))
 (hyl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left lty left)))
 (hyr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left rty right))) :
 Nonempty (Derivation body Delta (equal ltg rtg ⊓ equal lty rty)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := leftOf q1
 let qs : Fin 3 → Program 1 := ![q0,q1,q2]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![out.relabel j] : Fin 1 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.left q1 (ys 2) (ys 1) xx (hq 2) (hq 1)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hyl' := renameInto hyl j Theta hj
 have hyr' := renameInto hyr j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' hvl' hvr' htl' htr' hyl' hyr'
 have rootl := EvaluatorChildrenProjectionProof.recursiveRoot R H G M W (left.relabel j) (parameter.relabel j)
   (out.relabel j) (ys 0) (ys 1) hsl' hvl' h0 h1
 have etl := EvaluatorAlignmentTagRecoverProof.sourceTag (OriginalHereditaryEvaluatorDefinitions.evaluator R) H G M W
   (left.relabel j) (parameter.relabel j) (ltg.relabel j) (ys 1) (ys 2) hsl' htl' rootl h2
 have eql := etl
 rw [equalEqn] at eql
 have tagl := outputTransport OriginalRootObservation.tag (ltg.relabel j) (ys 2)
   (![ left.relabel j,parameter.relabel j]) eql htl'
 have rootr := EvaluatorChildrenProjectionProof.recursiveRoot R H G M W (right.relabel j) (parameter.relabel j)
   (out.relabel j) (ys 0) (ys 1) hsr' hvr' h0 h1
 have etr := EvaluatorAlignmentTagRecoverProof.sourceTag (OriginalHereditaryEvaluatorDefinitions.evaluator R) H G M W
   (right.relabel j) (parameter.relabel j) (rtg.relabel j) (ys 1) (ys 2) hsr' htr' rootr h2
 have eqr := etr
 rw [equalEqn] at eqr
 have tagr := outputTransport OriginalRootObservation.tag (rtg.relabel j) (ys 2)
   (![ right.relabel j,parameter.relabel j]) eqr htr'
 have htypes := EvaluatorAlignmentTypeDispatchProof.types (OriginalHereditaryEvaluatorDefinitions.evaluator R) H G M W
   (left.relabel j) (right.relabel j) (parameter.relabel j) (ys 2) (ys 1) (lty.relabel j) (rty.relabel j)
   hsl' hsr' tagl tagr rootl rootr hyl' hyr'
 simp only [conjunctionRename,equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 rw [equalEqn] at htypes
 obtain ⟨el⟩ := eql
 obtain ⟨er⟩ := eqr
 exact andIntro ⟨InternalTagArithmeticSupportProof.trans el (InternalTagArithmeticSupportProof.symm er)⟩ htypes
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentRootSharedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentRootSharedProof
