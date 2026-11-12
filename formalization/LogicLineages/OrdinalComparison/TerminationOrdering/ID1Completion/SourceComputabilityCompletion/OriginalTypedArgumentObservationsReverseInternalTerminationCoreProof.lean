module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsReverseInternalStepProof
open OriginalTypedArgumentObservationsReverseInternalBoundProof
open OriginalTypedArgumentObservationsReverseInternalTerminationDefinitions OriginalTypedArgumentObservationsReverseInternalTerminationBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (state acc out : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z state acc out))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left z out)) := by
 have hp := andLeft hf
 have hr := stopped (suc z) state acc hp
 obtain ⟨he⟩ := valueUnique reverseRun state out ![suc z,state] hr (andRight hf)
 exact headTransport InternalUnpair.left z state out Fin.elim0 ⟨he⟩ (pairLeft state z acc hp)

/-- The induction hypothesis concerns the actual tail run at an internally
queried result. No source interpretation or external termination premise. -/
theorem consValues (raw state acc out head tail nextAcc next middle result : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw state acc out)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next tail nextAcc)))
 (hm : Nonempty (Derivation body Delta (graph2 reverseRun middle (suc tail) next)))
 (hresult : Nonempty (Derivation body Delta (graph1 InternalUnpair.right result middle))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left z out)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have hz := belowRawApply raw tail next nextAcc middle hi hb (andIntro hn hm)
 have hp := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body alpha middle z result)
   (andIntro hz hresult)
 have hstep := stepCons state raw acc head tail nextAcc next (andLeft hf) hc ha hn
 have hrun := consFinish raw head tail state next middle result hc hstep hm hp
 obtain ⟨he⟩ := valueUnique reverseRun middle out ![suc raw,state] hrun (andRight hf)
 exact headTransport InternalUnpair.left z middle out Fin.elim0 ⟨he⟩ hz
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationCoreProof
