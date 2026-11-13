module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorApplicationEraseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsRebuildProof
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
theorem atLeftRebuilt (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha)
 (cutoff d deleted dp el er fl fr al ar : OTerm alpha)
 (fpl apl : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowLength R H G M W (suc count))))
 (hs : Nonempty (Derivation body Delta (applicationFields R H G M W (suc count) xs)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff (suc count))))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff (xs 15))))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff (xs 15))))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing dp (xs 14) deleted)))
 (heL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw el d cutoff (xs 0))))
 (heR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw er d cutoff (xs 1))))
 (hfL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw fl d cutoff (xs 2))))
 (hfR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw fr d cutoff (xs 3))))
 (haL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw al d cutoff (xs 4))))
 (haR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw ar d cutoff (xs 5))))
 (hcL : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors
  (xs 6) (xs 7) (xs 8) fpl apl fl al el))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W el er dp)) := by
 apply Context.EvaluatorApplicationEraseProof.actualApplicationErase body alpha Delta
  (xs 6) (xs 7) (xs 8) (xs 10) (xs 12) (xs 3) (xs 5) (xs 1) er fr ar d cutoff _
  (andLeft (andRight (andRight (andRight hs)))) heR hfR haR
 intro beta j Theta hj fpr apr hcR
 rw [EvaluatorErasureSyntax.admittedRename]
 have hi' := renameInto hi j Theta hj
 have hs' := renameInto hs j Theta hj
 have hb' := renameInto hb j Theta hj
 have hk' := renameInto hk j Theta hj
 have hd' := renameInto hd j Theta hj
 have hn' := renameInto hn j Theta hj
 have heL' := renameInto heL j Theta hj
 have heR' := renameInto heR j Theta hj
 have hfL' := renameInto hfL j Theta hj
 have hfR' := renameInto hfR j Theta hj
 have haL' := renameInto haL j Theta hj
 have haR' := renameInto haR j Theta hj
 have hcL' := renameInto hcL j Theta hj
 simp only [EvaluatorConstructorInductionSyntaxProof.belowLengthRename,sucRelabel,
  EvaluatorConstructorApplicationCellsSyntaxProof.fieldsRename,OriginalContextInsertion.Below,
  InternalOriginalOrderSyntaxProof.orderRename,graph2Rename,graph3Rename,
  InternalApplicationValidityClosure.applicationConstructors,
  InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph4Rename] at hi' hs' hb' hk' hd' hn' heL' heR' hfL' hfR' haL' haR' hcL'
 exact EvaluatorConstructorApplicationCellsCoreProof.atRebuilt R H G M W (count.relabel j) (fun i => (xs i).relabel j)
  (cutoff.relabel j) (d.relabel j) (deleted.relabel j) (dp.relabel j)
  (el.relabel j) (er.relabel j) (fl.relabel j) (fr.relabel j) (al.relabel j) (ar.relabel j)
  (fpl.relabel j) fpr (apl.relabel j) apr hi' hs' hb' hk' hd' hn' heL' heR' hfL' hfR' haL' haR' hcL' hcR

theorem atErasedChildren (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha)
 (cutoff d deleted dp el er fl fr al ar : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowLength R H G M W (suc count))))
 (hs : Nonempty (Derivation body Delta (applicationFields R H G M W (suc count) xs)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff (suc count))))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff (xs 15))))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff (xs 15))))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing dp (xs 14) deleted)))
 (heL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw el d cutoff (xs 0))))
 (heR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw er d cutoff (xs 1))))
 (hfL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw fl d cutoff (xs 2))))
 (hfR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw fr d cutoff (xs 3))))
 (haL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw al d cutoff (xs 4))))
 (haR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw ar d cutoff (xs 5)))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W el er dp)) := by
 apply Context.EvaluatorApplicationEraseProof.actualApplicationErase body alpha Delta
  (xs 6) (xs 7) (xs 8) (xs 9) (xs 11) (xs 2) (xs 4) (xs 0) el fl al d cutoff _
  (andLeft (andRight (andRight hs))) heL hfL haL
 intro beta j Theta hj fpl apl hcL
 rw [EvaluatorErasureSyntax.admittedRename]
 have hi' := renameInto hi j Theta hj
 have hs' := renameInto hs j Theta hj
 have hb' := renameInto hb j Theta hj
 have hk' := renameInto hk j Theta hj
 have hd' := renameInto hd j Theta hj
 have hn' := renameInto hn j Theta hj
 have heL' := renameInto heL j Theta hj
 have heR' := renameInto heR j Theta hj
 have hfL' := renameInto hfL j Theta hj
 have hfR' := renameInto hfR j Theta hj
 have haL' := renameInto haL j Theta hj
 have haR' := renameInto haR j Theta hj
 simp only [EvaluatorConstructorInductionSyntaxProof.belowLengthRename,sucRelabel,
  EvaluatorConstructorApplicationCellsSyntaxProof.fieldsRename,OriginalContextInsertion.Below,
  InternalOriginalOrderSyntaxProof.orderRename,graph2Rename,graph3Rename,
  InternalApplicationValidityClosure.applicationConstructors,
  InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph4Rename] at hi' hs' hb' hk' hd' hn' heL' heR' hfL' hfR' haL' haR'
 exact atLeftRebuilt R H G M W (count.relabel j) (fun i => (xs i).relabel j)
  (cutoff.relabel j) (d.relabel j) (deleted.relabel j) (dp.relabel j)
  (el.relabel j) (er.relabel j) (fl.relabel j) (fr.relabel j) (al.relabel j) (ar.relabel j)
  fpl apl hi' hs' hb' hk' hd' hn' heL' heR' hfL' hfR' haL' haR' hcL

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsRebuildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsRebuildProof
