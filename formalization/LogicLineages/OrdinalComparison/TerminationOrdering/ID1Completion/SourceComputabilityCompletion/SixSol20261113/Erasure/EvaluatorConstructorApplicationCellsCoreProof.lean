module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationDeletedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorDeletionMetadataProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsCoreProof
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
theorem atRebuilt (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha)
 (cutoff d deleted dp el er fl fr al ar : OTerm alpha)
 (fpl fpr apl apr : OTerm alpha)
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
  (xs 6) (xs 7) (xs 8) fpl apl fl al el)))
 (hcR : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors
  (xs 6) (xs 7) (xs 8) fpr apr fr ar er))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W el er dp)) := by
 have sL := andLeft hs
 have sR := andLeft (andRight hs)
 have pairF := andLeft (andRight (andRight (andRight (andRight hs))))
 have pairA := andLeft (andRight (andRight (andRight (andRight (andRight hs)))))
 have param := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hs))))))
 have len := andRight (andRight (andRight (andRight (andRight (andRight (andRight hs))))))
 obtain ⟨ins,newLen,less⟩ := EvaluatorConstructorDeletionMetadataProof.atSuccessor count (xs 15) cutoff deleted d len hb hd hk
 exact EvaluatorConstructorApplicationDeletedProof.atCoordinates R H G M W
  (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 13) (xs 14) (xs 15)
  deleted dp cutoff d (suc count) count
  ![el,er,fl,fr,al,ar,xs 6,xs 7,xs 8,fpl,fpr,apl,apr,dp,xs 14,deleted]
  hi less sL sR pairF pairA param hn len hb hk hd ins
  heL heR hfL hfR haL haR hcL hcR newLen rfl rfl rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsCoreProof
