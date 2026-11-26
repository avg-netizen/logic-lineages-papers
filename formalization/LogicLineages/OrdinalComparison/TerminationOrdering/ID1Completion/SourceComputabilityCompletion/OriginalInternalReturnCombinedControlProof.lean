module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnCombinedControlProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem control (R : Program 2) (input work results frame rest payload out : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) out input)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hwork := OriginalHereditaryInternalVisitSupportProof.workGraph input work results hs
 have hframe := OriginalHereditaryInternalVisitSupportProof.frameGraph input work results frame rest hs hw
 have htag : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryCombinedStep.frame) (numeral 1) input)) :=
  unaryValue InternalUnpair.left OriginalHereditaryCombinedStep.frame (numeral 1) frame xs (pairLeft frame (numeral 1) payload hf) hframe
 have hy := sameYesIntro (leftOf OriginalHereditaryCombinedStep.frame) (OriginalRawSyntaxTransport.constant 1 1)
  (OriginalHereditaryReturnStep.step R) (.projection 0) out (numeral 1) (numeral 1) xs htag (constantValue 1 xs)
  (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 1)))) hr
 have hn := sameNoIntro (leftOf OriginalHereditaryCombinedStep.frame) (OriginalRawSyntaxTransport.constant 1 0)
  OriginalHereditaryAnnotatedVisit.step (OriginalTypedDecoder.ifSame (leftOf OriginalHereditaryCombinedStep.frame) (OriginalRawSyntaxTransport.constant 1 1) (OriginalHereditaryReturnStep.step R) (.projection 0))
  out (numeral 1) (numeral 0) xs htag (constantValue 0 xs) (numeralNe 1 0 (by decide)) hy
 exact InternalApplicationResultStackReturnSupportProof.nonzeroBranchIntro OriginalHereditaryCombinedStep.work (.projection 0)
  _ out work xs hwork (OriginalTypedDecoderInternalListProof.consNonzero work frame rest hw) hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnCombinedControlProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnCombinedControlProof
