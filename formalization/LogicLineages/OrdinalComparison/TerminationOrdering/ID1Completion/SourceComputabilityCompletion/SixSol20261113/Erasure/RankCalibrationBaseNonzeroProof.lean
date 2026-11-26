module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseEnvelopeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseNonzeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem actualNonvariableNonzero : RankCalibrationBaseTargets.ActualNonvariableNonzero := by
 intro R H G M W body alpha Delta input parameter code k hs hv ht
 let qs : Fin 7 → Program 2 := ![leftOf (.projection 0),rightOf (.projection 0),
   leftOf (.projection 1),rightOf (.projection 1),leftOf (rightOf (.projection 1)),
   rightOf (rightOf (.projection 1)),leftOf (leftOf (rightOf (.projection 1)))]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (![input,code]) _
 intro beta j ys Theta hj hq
 let xs : Fin 2 → OTerm beta := ![input.relabel j,code.relabel j]
 have hx : (fun a : Fin 2 => (![input,code] a).relabel j) = xs := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have ip := reconstructPair (input.relabel j) (ys 0) (ys 1)
   (unaryRecover InternalUnpair.left (.projection 0) (ys 0) (input.relabel j) xs (hq 0) (projectionValue 0 xs))
   (unaryRecover InternalUnpair.right (.projection 0) (ys 1) (input.relabel j) xs (hq 1) (projectionValue 0 xs))
 have op := reconstructPair (code.relabel j) (ys 2) (ys 3)
   (unaryRecover InternalUnpair.left (.projection 1) (ys 2) (code.relabel j) xs (hq 2) (projectionValue 1 xs))
   (unaryRecover InternalUnpair.right (.projection 1) (ys 3) (code.relabel j) xs (hq 3) (projectionValue 1 xs))
 have inn := reconstructPair (ys 3) (ys 4) (ys 5)
   (unaryRecover InternalUnpair.left (rightOf (.projection 1)) (ys 4) (ys 3) xs (hq 4) (hq 3))
   (unaryRecover InternalUnpair.right (rightOf (.projection 1)) (ys 5) (ys 3) xs (hq 5) (hq 3))
 have lab := unaryRecover InternalUnpair.left (leftOf (rightOf (.projection 1))) (ys 6) (ys 4) xs (hq 6) (hq 4)
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs' hv' ht'
 simp only [OriginalTypedDecoderTransportLogicalProof.notRename,OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,GuardedSourceSyntaxProof.numeralRename]
 exact RankCalibrationBaseEnvelopeProof.atEnvelope R H G M W k
   (input.relabel j) (parameter.relabel j) (ys 0) (ys 1) (code.relabel j) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)
   hs' hv' ip ht' op inn lab
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseNonzeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseNonzeroProof
