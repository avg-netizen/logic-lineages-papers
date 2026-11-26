module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof (orderRight orderLeft rightSuccessor)
open InternalAdditionLawsProof (add)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open InternalPairingSumBoundsArithmeticProof (addWeakLeft)
open InternalPairingSumBounds (weakBound)
open InternalRecursionClosureLogicProof (closedApply)
open ListSumInductionDefinitions ListSumInductionSyntaxProof ListSumInductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sumNil : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum z z)) :=
 SortWeightedFoldProof.nilValue (.projection (0 : Fin 1)) Fin.elim0

theorem sumConsEqual (raw head tail total tailSum : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ht : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum tailSum tail)))
 (hs : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum total raw))) :
 Nonempty (Derivation body Delta (eqn total (add head tailSum))) :=
 SortWeightedFoldProof.consUnique (.projection (0 : Fin 1)) raw head tail head tailSum total Fin.elim0 hc
   (projectionValue 0 (Fin.cons head Fin.elim0)) ht hs

theorem sumConsBoundAtPair (raw head tail pair : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair head tail))) :
 Nonempty (Derivation body Delta (weakBound (add head tail) raw)) := by
 obtain ⟨he⟩ := valueUnique InternalListCodec.consCode raw (suc pair) (Fin.cons head (Fin.cons tail Fin.elim0))
   hc (InternalListCodecSupportProof.consValue pair head tail hp)
 obtain ⟨hb⟩ := closedApply (InternalPairingSumBoundsProof.actualOriginalPairingSumBound body alpha pair head tail) hp
 exact rightSuccessor (add head tail) raw ⟨orderRight (add head tail) (symm he) hb⟩

theorem sumConsBound (raw head tail : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail))) :
 Nonempty (Derivation body Delta (weakBound (add head tail) raw)) := by
 apply programCases InternalPairing.pairing (Fin.cons head (Fin.cons tail Fin.elim0)) _
 intro beta j Theta pair hj hp
 simp only [weakBound,InternalLessThan.strictLess,orderRename,sucRelabel,InternalOriginalOrderSyntaxProof.addRelabel]
 simp only [consTermRename,emptyRename] at hp
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 exact sumConsBoundAtPair (raw.relabel j) (head.relabel j) (tail.relabel j) pair hc' hp

theorem zeroCore (raw total : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn raw z)))
 (hs : Nonempty (Derivation body Delta (fields raw total))) :
 Nonempty (Derivation body Delta (result raw total)) := by
 have hs' := headTransport ListSumBoundDefinitions.sum total raw z Fin.elim0 he hs
 obtain ⟨ht⟩ := valueUnique ListSumBoundDefinitions.sum total z (Fin.cons z Fin.elim0) hs' sumNil
 obtain ⟨he⟩ := he
 exact ⟨InternalQuotientComparisonProof.equalToNext (InternalTagArithmeticSupportProof.trans ht (symm he))⟩

theorem consCore (raw head tail total tailSum : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hs : Nonempty (Derivation body Delta (fields raw total)))
 (ht : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum tailSum tail))) :
 Nonempty (Derivation body Delta (result raw total)) := by
 have hd := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have hb := belowRawApply raw tail tailSum hi hd ht
 obtain ⟨he⟩ := sumConsEqual raw head tail total tailSum hc ht hs
 obtain ⟨hb'⟩ := weakTrans (add head tailSum) (add head tail) raw
   (addWeakLeft head tailSum tail hb) (sumConsBound raw head tail hc)
 exact ⟨orderLeft (suc raw) (symm he) hb'⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumCoreProof
