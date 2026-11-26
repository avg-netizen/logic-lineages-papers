module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupCore
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
open ObservationDescentLookupDefinitions ObservationDescentLookupSyntaxProof ObservationDescentLookupBindingProof
open ObservationDescentPairProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem headAtPair (raw head tail pair : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair head tail))) :
 Nonempty (Derivation body Delta (ltF head raw)) := by
 obtain ⟨he⟩ := valueUnique InternalListCodec.consCode raw (suc pair) ![head,tail] hc (consValue pair head tail hp)
 obtain ⟨hb⟩ := pairLeftBound pair head tail hp
 exact ⟨orderRight head (symm he) hb⟩

theorem consHead (raw head tail : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail))) :
 Nonempty (Derivation body Delta (ltF head raw)) := by
 apply programCases InternalPairing.pairing (Fin.cons head (Fin.cons tail Fin.elim0)) _
 intro beta j Theta pair hj hp
 rw [orderRename]
 simp only [consTermRename,emptyRename] at hp
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 exact headAtPair (raw.relabel j) (head.relabel j) (tail.relabel j) pair hc' hp

theorem atZero (raw head tail count index value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value)))
 (he : Nonempty (Derivation body Delta (eqn index z))) :
 Nonempty (Derivation body Delta (ltF value raw)) := by
 have hl := headTransport InternalRawListRecursion.lookup value index z ![raw] he (andRight (andRight hf))
 obtain ⟨heq⟩ := valueUnique InternalRawListRecursion.lookup value head ![z,raw] hl
   (OriginalAllPositionContextDeleteBaseProof.lookupZero raw head tail hc)
 obtain ⟨hb⟩ := consHead raw head tail hc
 exact ⟨orderLeft raw (symm heq) hb⟩

theorem atSuccessor (raw head tail count index value pred tailCount : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value)))
 (he : Nonempty (Derivation body Delta (eqn index (suc pred))))
 (ht : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph tailCount tail))) :
 Nonempty (Derivation body Delta (ltF value raw)) := by
 obtain ⟨hlen⟩ := OriginalContextInsertionLengthProof.lengthConsRecover raw head tail count tailCount hc (andLeft hf) ht
 obtain ⟨hb⟩ := andLeft (andRight hf)
 obtain ⟨he⟩ := he
 have hb' := OriginalContextInsertionBelowCoreProof.successorStrict pred tailCount
   ⟨orderRight (suc pred) hlen (orderLeft count he hb)⟩
 have hl := headTransport InternalRawListRecursion.lookup value index (suc pred) ![raw] ⟨he⟩ (andRight (andRight hf))
 obtain ⟨hiff⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff raw head tail pred value hc
 obtain ⟨hl⟩ := hl
 have htlookup := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft hiff) hl)
 have hdescent := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have hv := belowRawApply raw tail tailCount pred value hi hdescent (andIntro ht (andIntro hb' htlookup))
 exact strictTrans value tail raw hv hdescent
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupCore
