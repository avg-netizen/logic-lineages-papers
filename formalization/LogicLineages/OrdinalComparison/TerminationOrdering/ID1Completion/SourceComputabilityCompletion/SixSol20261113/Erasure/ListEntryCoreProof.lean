module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalTagArithmeticSupportProof (symm)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof (orderRight orderLeft strictTrans)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof (consValue)
open ListEntryInductionDefinitions ListEntryInductionSyntaxProof ListEntryInductionBindingProof
open ObservationDescentPairProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAdditionLawsProof (add)
open InternalUnpairArithmeticProof (leftWeakAdd)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans rightWeakAdd)
open InternalTagArithmeticSupportProof (congSuc)

theorem atZero (raw head tail count index value total tailSum : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value total)))
 (he : Nonempty (Derivation body Delta (eqn index z)))
 (ht : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum tailSum tail))) :
 Nonempty (Derivation body Delta (result raw count index value total)) := by
 have hl := headTransport InternalRawListRecursion.lookup value index z ![raw] he
   (andLeft (andRight (andRight hf)))
 obtain ⟨heq⟩ := valueUnique InternalRawListRecursion.lookup value head ![z,raw] hl
   (OriginalAllPositionContextDeleteBaseProof.lookupZero raw head tail hc)
 obtain ⟨hs⟩ := ListSumCoreProof.sumConsEqual raw head tail total tailSum hc ht (andRight (andRight (andRight hf)))
 obtain ⟨hb⟩ := leftWeakAdd (body := body) (Gamma := Delta) head tailSum
 exact ⟨orderLeft (suc total) (symm heq)
   (orderRight head (congSuc (symm hs)) hb)⟩

theorem atSuccessor (raw head tail count index value total pred tailCount tailSum : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value total)))
 (he : Nonempty (Derivation body Delta (eqn index (suc pred))))
 (ht : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph tailCount tail)))
 (hts : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum tailSum tail))) :
 Nonempty (Derivation body Delta (result raw count index value total)) := by
 obtain ⟨hlen⟩ := OriginalContextInsertionLengthProof.lengthConsRecover raw head tail count tailCount hc (andLeft hf) ht
 obtain ⟨hb⟩ := andLeft (andRight hf)
 obtain ⟨he⟩ := he
 have hb' := OriginalContextInsertionBelowCoreProof.successorStrict pred tailCount
   ⟨orderRight (suc pred) hlen (orderLeft count he hb)⟩
 have hl := headTransport InternalRawListRecursion.lookup value index (suc pred) ![raw] ⟨he⟩
   (andLeft (andRight (andRight hf)))
 obtain ⟨hiff⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff raw head tail pred value hc
 obtain ⟨hl⟩ := hl
 have htlookup := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft hiff) hl)
 have hd := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have hv := belowRawApply raw tail tailCount pred value tailSum hi hd
   (andIntro ht (andIntro hb' (andIntro htlookup hts)))
 obtain ⟨hs⟩ := ListSumCoreProof.sumConsEqual raw head tail total tailSum hc hts (andRight (andRight (andRight hf)))
 obtain ⟨hv'⟩ := weakTrans value tailSum (add head tailSum) hv (rightWeakAdd head tailSum)
 exact ⟨orderRight value (congSuc (symm hs)) hv'⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryCoreProof
