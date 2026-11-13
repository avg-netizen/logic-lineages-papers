module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsRebuildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsChildQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsMetadataProof
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
theorem atMetadata (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha)
 (cutoff d deleted dp el er : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowLength R H G M W (suc count))))
 (hs : Nonempty (Derivation body Delta (applicationFields R H G M W (suc count) xs)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff (suc count))))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff (xs 15))))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff (xs 15))))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing dp (xs 14) deleted)))
 (heL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw el d cutoff (xs 0))))
 (heR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw er d cutoff (xs 1)))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W el er dp)) := by
 apply EvaluatorConstructorApplicationCellsChildQueries.actualCases d cutoff ![xs 2,xs 3,xs 4,xs 5] _
 intro beta j Theta outs hj hq
 rw [EvaluatorErasureSyntax.admittedRename]
 have hi' := renameInto hi j Theta hj
 have hs' := renameInto hs j Theta hj
 have hb' := renameInto hb j Theta hj
 have hk' := renameInto hk j Theta hj
 have hd' := renameInto hd j Theta hj
 have hn' := renameInto hn j Theta hj
 have heL' := renameInto heL j Theta hj
 have heR' := renameInto heR j Theta hj
 simp only [EvaluatorConstructorInductionSyntaxProof.belowLengthRename,sucRelabel,
  EvaluatorConstructorApplicationCellsSyntaxProof.fieldsRename,OriginalContextInsertion.Below,
  InternalOriginalOrderSyntaxProof.orderRename,graph2Rename,graph3Rename] at hi' hs' hb' hk' hd' hn' heL' heR'
 exact EvaluatorConstructorApplicationCellsRebuildProof.atErasedChildren R H G M W
  (count.relabel j) (fun i => (xs i).relabel j) (cutoff.relabel j) (d.relabel j)
  (deleted.relabel j) (dp.relabel j) (el.relabel j) (er.relabel j) (outs 0) (outs 1) (outs 2) (outs 3)
  hi' hs' hb' hk' hd' hn' heL' heR' (hq 0) (hq 1) (hq 2) (hq 3)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsMetadataProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsMetadataProof
