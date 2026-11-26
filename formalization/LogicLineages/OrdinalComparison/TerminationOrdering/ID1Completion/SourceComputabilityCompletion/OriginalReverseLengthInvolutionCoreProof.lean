module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedArgumentObservations (reverse)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalReverseLengthInvolutionDefinitions OriginalReverseLengthInvolutionSyntaxProof OriginalReverseLengthInvolutionBindingProof

theorem zeroCore (raw count mapped : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields raw count mapped))) :
 Nonempty (Derivation body Delta (outputs raw count mapped)) := by
 have hm := headTransport reverse mapped raw z Fin.elim0 he (andRight hf)
 have em := valueUnique reverse mapped z (Fin.cons z Fin.elim0) hm OriginalReverseConsProof.zero
 have hl := headTransport OriginalContextInsertion.length count raw mapped Fin.elim0
   ⟨trans (Classical.choice he) (symm (Classical.choice em))⟩ (andLeft hf)
 have hv := headTransport reverse z z mapped Fin.elim0 ⟨symm (Classical.choice em)⟩ OriginalReverseConsProof.zero
 have hr := outputTransport reverse z raw (Fin.cons mapped Fin.elim0) ⟨symm (Classical.choice he)⟩ hv
 exact andIntro hl hr

theorem consValues (raw head tail count mapped tailCount tailMapped singleton actual : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw count mapped)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length tailCount tail)))
 (hm : Nonempty (Derivation body Delta (graph1 reverse tailMapped tail)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton head z)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append actual tailMapped singleton))) :
 Nonempty (Derivation body Delta (outputs raw count mapped)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have ih := belowRawApply raw tail tailCount tailMapped hi hb (andIntro hl hm)
 have hv := OriginalReverseConsProof.actualCons body alpha Delta raw head tail singleton tailMapped actual hc hs hm ha
 have em := valueUnique reverse actual mapped (Fin.cons raw Fin.elim0) hv (andRight hf)
 have hlen := OriginalHereditaryDeletionRowsLengthProof.appendSingletonLength tailCount tailMapped head singleton actual
   (andLeft ih) hs ha
 have hrawlen := OriginalContextInsertionLengthProof.lengthCons raw head tail tailCount hc hl
 have ec := valueUnique OriginalContextInsertion.length (suc tailCount) count (Fin.cons raw Fin.elim0) hrawlen (andLeft hf)
 have hlen' := headTransport OriginalContextInsertion.length (suc tailCount) actual mapped Fin.elim0 em hlen
 have hlen'' := outputTransport OriginalContextInsertion.length (suc tailCount) count (Fin.cons mapped Fin.elim0) ec hlen'
 have hr := OriginalTypedArgumentObservationsReverseInternalProof.backward tailMapped head singleton actual tail raw
   hs ha (andRight ih) hc
 exact andIntro hlen'' (headTransport reverse raw actual mapped Fin.elim0 em hr)

theorem atThree (raw head tail count mapped tailCount tailMapped singleton : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw count mapped)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length tailCount tail)))
 (hm : Nonempty (Derivation body Delta (graph1 reverse tailMapped tail)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton head z))) :
 Nonempty (Derivation body Delta (outputs raw count mapped)) := by
 apply programCases InternalApplicationValidityStackAppend.append (Fin.cons tailMapped (Fin.cons singleton Fin.elim0)) _
 intro beta rho Theta actual hrho ha
 simp only [consTermRename,emptyRename] at ha
 simp only [outputs,conjunctionRename,graph1Rename]
 have hi' := renameInto hi rho Theta hrho
 rw [belowRawRename] at hi'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename] at hf'
 have hc' := renameInto hc rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 have hm' := renameInto hm rho Theta hrho
 have hs' := renameInto hs rho Theta hrho
 simp only [graph2Rename,zRelabel] at hc' hs'
 rw [graph1Rename] at hl' hm'
 exact consValues (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (count.relabel rho)
   (mapped.relabel rho) (tailCount.relabel rho) (tailMapped.relabel rho) (singleton.relabel rho) actual hi' hf' hc' hl' hm' hs' ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionCoreProof
