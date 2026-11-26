module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsMetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions EvaluatorErasureSyntax EvaluatorConstructorInductionDefinitions
open EvaluatorConstructorInductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalHereditaryDeletionRowsCongruence
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open InternalOriginalOrderSyntaxProof (orderRename)
theorem actualCells (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowLength R H G M W (suc count))))
 (hs : Nonempty (Derivation body Delta (applicationFields R H G M W (suc count) xs))) :
 Nonempty (Derivation body Delta (CellAgreement (OriginalHereditaryEvaluatorDefinitions.evaluator R)
  (suc count) (xs 0) (xs 13) (xs 1) (xs 13))) := by
 apply EvaluatorConstructorCellBindingProof.introduction
 intro beta j Theta index a b hj hb ha hc
 have hi' := renameInto hi j Theta hj
 have hs' := renameInto hs j Theta hj
 simp only [EvaluatorConstructorInductionSyntaxProof.belowLengthRename,sucRelabel] at hi'
 simp only [EvaluatorConstructorApplicationCellsSyntaxProof.fieldsRename,sucRelabel] at hs'
 simp only [sucRelabel] at hb
 apply EvaluatorConstructorCellQueries.actualCases ((xs 0).relabel j) ((xs 1).relabel j)
  ((xs 15).relabel j) ((xs 14).relabel j) index _
 intro eta k Xi d deleted dp el er hk hlook hdel hparam heL heR
 rw [equalRename]
 have hi'' := renameInto hi' k Xi hk
 have hs'' := renameInto hs' k Xi hk
 have hb' := renameInto hb k Xi hk
 have ha' := renameInto ha k Xi hk
 have hc' := renameInto hc k Xi hk
 simp only [EvaluatorConstructorInductionSyntaxProof.belowLengthRename,sucRelabel] at hi''
 simp only [EvaluatorConstructorApplicationCellsSyntaxProof.fieldsRename,sucRelabel] at hs''
 simp only [OriginalContextInsertion.Below,orderRename,sucRelabel] at hb'
 rw [graph3Rename] at ha' hc'
 have pair := EvaluatorConstructorApplicationCellsMetadataProof.atMetadata R H G M W
  ((count.relabel j).relabel k) (fun i => ((xs i).relabel j).relabel k)
  (index.relabel k) d deleted dp el er hi'' hs'' hb' hlook hdel hparam heL heR
 have hp := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hs''))))))
 have eq := EvaluatorConstructorCellProof.atGeometry R
  (((xs 0).relabel j).relabel k) (((xs 1).relabel j).relabel k) el er
  (((xs 13).relabel j).relabel k) dp (((xs 14).relabel j).relabel k)
  (((xs 15).relabel j).relabel k) deleted (index.relabel k) d (a.relabel k) (b.relabel k)
  hp hparam hlook hdel heL heR (andRight (andRight pair)) ha' hc'
 rw [equalEqn]
 exact eq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsProof
