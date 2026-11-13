module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LambdaContextDeletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalContextInsertionSyntaxProof (lengthRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorConstructorInductionDefinitions EvaluatorConstructorInductionSyntaxProof
open EvaluatorConstructorFieldsSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atParentGeometry (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 11 → OTerm alpha)
 (cutoff d deleted newParameter erasedLeft erasedRight a b : OTerm alpha)
 (hIH : Nonempty (Derivation body Delta (BelowLength R H G M W (suc count))))
 (hf : Nonempty (Derivation body Delta (lambdaFields R H G M W (suc count) xs)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff (suc count))))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff (xs 9))))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff (xs 9))))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParameter (xs 8) deleted)))
 (heL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedLeft d cutoff (xs 0))))
 (heR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedRight d cutoff (xs 1))))
 (ha : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) a cutoff (xs 0) (xs 6))))
 (hbb : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) b cutoff (xs 1) (xs 6))))
 : Nonempty (Derivation body Delta (equal a b)) := by
 apply EvaluatorConstructorLambdaCellQueries.actualCases d cutoff (xs 2) (xs 3) (xs 4) (xs 8) deleted (xs 5) _
 intro beta j Theta ecl ecr cd cp arrow hj hecl hecr hcd hcp harr
 rw [equalRename]
 have hIH' := renameInto hIH j Theta hj
 have hf' := renameInto hf j Theta hj
 have hb' := renameInto hb j Theta hj
 have hk' := renameInto hk j Theta hj
 have hd' := renameInto hd j Theta hj
 have hn' := renameInto hn j Theta hj
 have heL' := renameInto heL j Theta hj
 have heR' := renameInto heR j Theta hj
 have ha' := renameInto ha j Theta hj
 have hbb' := renameInto hbb j Theta hj
 simp only [belowLengthRename,sucRelabel] at hIH'
 simp only [lambdaRename,sucRelabel] at hf'
 simp only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename,sucRelabel] at hb'
 simp only [graph2Rename,graph3Rename] at hk' hd' hn' heL' heR' ha' hbb'
 have h3 := andLeft (andRight (andRight (andRight hf')))
 have h10 := (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf'))))))))))
 have metadata := Context.LambdaContextDeletionProof.actualMetadata body beta Theta
   ((xs 9).relabel j) (deleted.relabel j) ((xs 10).relabel j) cd ((xs 4).relabel j)
   (cutoff.relabel j) (d.relabel j) (suc (count.relabel j)) h3 hcd h10 hb' hk' hd'
 have result := EvaluatorConstructorLambdaCellGeometryProof.atGeometry R H G M W
   (count.relabel j) (fun i => (xs i).relabel j)
   (cutoff.relabel j) (d.relabel j) (deleted.relabel j) (newParameter.relabel j)
   (erasedLeft.relabel j) (erasedRight.relabel j) ecl ecr cd cp arrow (a.relabel j) (b.relabel j)
   hIH' hf' hb' hk' hd' hn' heL' heR' hecl hecr hcd hcp harr
   (andLeft metadata) (andLeft (andRight metadata)) (andLeft (andRight (andRight metadata)))
   (andRight (andRight (andRight metadata))) ha' hbb'
 simpa only [equalEqn] using result
/-- Complete internally quantified lambda deletion-cell agreement. Every
metadata value is queried; only the actual smaller-context IH is consumed. -/
theorem actualCells (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 11 → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowLength R H G M W (suc count))))
 (hf : Nonempty (Derivation body Delta (lambdaFields R H G M W (suc count) xs))) :
 Nonempty (Derivation body Delta (OriginalHereditaryDeletionRowsCongruence.CellAgreement
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc count) (xs 0) (xs 6) (xs 1) (xs 6))) := by
 apply EvaluatorConstructorCellBindingProof.introduction (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   (suc count) (xs 0) (xs 1) (xs 6)
 intro beta j Theta index a b hj hb ha hbb
 have hi' := renameInto hi j Theta hj
 have hf' := renameInto hf j Theta hj
 simp only [belowLengthRename,sucRelabel] at hi'
 simp only [lambdaRename,sucRelabel] at hf'
 simp only [sucRelabel] at hb
 apply EvaluatorConstructorCellQueries.actualCases ((xs 0).relabel j) ((xs 1).relabel j)
   ((xs 9).relabel j) ((xs 8).relabel j) index _
 intro beta2 k Omega d deleted par el er hk hlook hdel hpar hel her
 rw [equalRename]
 have hi'' := renameInto hi' k Omega hk
 have hf'' := renameInto hf' k Omega hk
 have hb' := renameInto hb k Omega hk
 have ha' := renameInto ha k Omega hk
 have hbb' := renameInto hbb k Omega hk
 simp only [belowLengthRename,sucRelabel] at hi''
 simp only [lambdaRename,sucRelabel] at hf''
 simp only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename,sucRelabel] at hb'
 simp only [graph3Rename] at ha' hbb'
 exact atParentGeometry R H G M W ((count.relabel j).relabel k)
   (fun i => ((xs i).relabel j).relabel k) (index.relabel k) d deleted par el er (a.relabel k) (b.relabel k)
   hi'' hf'' hb' hlook hdel hpar hel her ha' hbb'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellsProof
