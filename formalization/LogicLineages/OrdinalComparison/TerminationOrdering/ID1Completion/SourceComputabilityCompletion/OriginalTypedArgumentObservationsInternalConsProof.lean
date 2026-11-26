module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReversedConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTypedArgumentObservations
open OriginalTypedArgumentObservationsReversedConsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem forward (R : Program 2) (raw typ child tail packed observation typedObservation mappedTail parameter out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (ho : Nonempty (Derivation body Delta (graph2 R observation packed parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedObservation typ observation)))
 (hm : Nonempty (Derivation body Delta (graph2 (argumentObservations R) mappedTail tail parameter)))
 (hout : Nonempty (Derivation body Delta (graph2 (argumentObservations R) out raw parameter)))
 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out typedObservation mappedTail)) := by
 apply reversedConsCases R raw typ child tail packed observation typedObservation parameter _ hc hp ho ht
 intro beta rho Theta singleton combined tailReversed hrho hs hj hparent htail
 simp only [graph2Rename]
 have hm' := renameInto hm rho Theta hrho
 simp only [graph2Rename] at hm'
 have hout' := renameInto hout rho Theta hrho
 simp only [graph2Rename] at hout'
 have htailReverse := unaryRecover reverse (reversedObservations R) (mappedTail.relabel rho) tailReversed
   ![tail.relabel rho,parameter.relabel rho] hm' htail
 have hparentReverse := unaryRecover reverse (reversedObservations R) (out.relabel rho) combined
   ![raw.relabel rho,parameter.relabel rho] hout' hparent
 exact OriginalTypedArgumentObservationsReverseInternalProof.forward tailReversed
   (typedObservation.relabel rho) singleton combined (mappedTail.relabel rho) (out.relabel rho)
   hs hj htailReverse hparentReverse

theorem backward (R : Program 2) (raw typ child tail packed observation typedObservation mappedTail parameter out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (ho : Nonempty (Derivation body Delta (graph2 R observation packed parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedObservation typ observation)))
 (hm : Nonempty (Derivation body Delta (graph2 (argumentObservations R) mappedTail tail parameter)))
 (hout : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out typedObservation mappedTail)))
 : Nonempty (Derivation body Delta (graph2 (argumentObservations R) out raw parameter)) := by
 apply reversedConsCases R raw typ child tail packed observation typedObservation parameter _ hc hp ho ht
 intro beta rho Theta singleton combined tailReversed hrho hs hj hparent htail
 simp only [graph2Rename]
 have hm' := renameInto hm rho Theta hrho
 simp only [graph2Rename] at hm'
 have hout' := renameInto hout rho Theta hrho
 simp only [graph2Rename] at hout'
 have htailReverse := unaryRecover reverse (reversedObservations R) (mappedTail.relabel rho) tailReversed
   ![tail.relabel rho,parameter.relabel rho] hm' htail
 have hr := OriginalTypedArgumentObservationsReverseInternalProof.backward tailReversed
   (typedObservation.relabel rho) singleton combined (mappedTail.relabel rho) (out.relabel rho)
   hs hj htailReverse hout'
 exact unaryValue reverse (reversedObservations R) (out.relabel rho) combined
   ![raw.relabel rho,parameter.relabel rho] hr hparent

theorem internalCons : OriginalTypedArgumentObservationsTargets.InternalCons := by
 intro R body alpha raw typ child tail packed observation typedObservation mappedTail parameter out
 let H := graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail ⊓
   (graph2 InternalPairing.pairing packed typ child ⊓
   (graph2 R observation packed parameter ⊓
   (graph2 InternalPairing.pairing typedObservation typ observation ⊓
    graph2 (argumentObservations R) mappedTail tail parameter)))
 let P := graph2 (argumentObservations R) out raw parameter
 let Q := graph2 InternalListCodec.consCode out typedObservation mappedTail
 have h : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hc := andLeft h
 have hp := andLeft (andRight h)
 have ho := andLeft (andRight (andRight h))
 have ht := andLeft (andRight (andRight (andRight h)))
 have hm := andRight (andRight (andRight (andRight h)))
 have hf : Nonempty (Derivation body (P :: [H]) Q) :=
   forward R raw typ child tail packed observation typedObservation mappedTail parameter out
     (withHyp hc P) (withHyp hp P) (withHyp ho P) (withHyp ht P) (withHyp hm P)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hb : Nonempty (Derivation body (Q :: [H]) P) :=
   backward R raw typ child tail packed observation typedObservation mappedTail parameter out
     (withHyp hc Q) (withHyp hp Q) (withHyp ho Q) (withHyp ht Q) (withHyp hm Q)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hf⟩ := hf
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
   (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
