module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentBranchesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTagProof
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
theorem liftTag (input parameter typ raw label : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag label input))) :
 Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag label input parameter)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 have hr := unaryValue InternalUnpair.right (.projection 0) raw input xs
   (pairRight input typ raw hp) (projectionValue 0 xs)
 have hl := unaryRecover InternalUnpair.left (rightOf (.projection 0)) label raw xs ht hr
 let ys : Fin 2 → OTerm alpha := ![input,parameter]
 have hr' := unaryValue InternalUnpair.right (.projection 0) raw input ys
   (pairRight input typ raw hp) (projectionValue 0 ys)
 exact unaryValue InternalUnpair.left OriginalRootObservation.raw label raw ys hl hr'

theorem observedTag (R : Program 2) (H G : Program 1) (M W : Program 2)
 (k : Fin 6) (input parameter typ raw code base inner root rows observed : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code input parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral k.val) input)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observed root))) :
 Nonempty (Derivation body Delta (equal observed (numeral k.val))) := by
 have htag := liftTag input parameter typ raw (numeral k.val) hp ht
 have hroot := Context.EvaluatorChildrenProjectionProof.recursiveRoot R H G M W input parameter code inner root hs hv
   (pairRight code base inner ho) (pairLeft inner root rows hi)
 revert htag
 refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))) k
 · intro htag
   exact Context.EvaluatorAlignmentBranchesProof.tag0 (OriginalHereditaryEvaluatorDefinitions.evaluator R) input parameter root observed htag hroot hl
 · intro htag
   exact Context.EvaluatorAlignmentBranchesProof.tag1 (OriginalHereditaryEvaluatorDefinitions.evaluator R) input parameter root observed htag hroot hl
 · intro htag
   exact Context.EvaluatorAlignmentBranchesProof.tag2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) input parameter root observed htag hroot hl
 · intro htag
   exact Context.EvaluatorAlignmentBranchesProof.tag3 (OriginalHereditaryEvaluatorDefinitions.evaluator R) input parameter root observed htag hroot hl
 · intro htag
   exact Context.EvaluatorAlignmentBranchesProof.tag4 (OriginalHereditaryEvaluatorDefinitions.evaluator R) input parameter root observed htag hroot hl
 · intro htag
   exact Context.EvaluatorAlignmentBranchesProof.tag5 (OriginalHereditaryEvaluatorDefinitions.evaluator R) input parameter root observed htag hroot hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTagProof
