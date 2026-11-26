module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem control (R : Program 2) (input work results frame rest payload out : OTerm alpha)
 (hstate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hwork : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hv : Nonempty (Derivation body Delta (graph1
   (OriginalTypedDecoder.ifSame OriginalHereditaryReturnStep.role (OriginalRawSyntaxTransport.constant 1 0)
     (OriginalHereditaryReturnStep.pop (OriginalHereditaryReturnStep.termValue R))
     (OriginalTypedDecoder.ifSame OriginalHereditaryReturnStep.role (OriginalRawSyntaxTransport.constant 1 1)
       OriginalHereditaryReturnStep.listStep (.projection 0))) out input))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 have hi : Nonempty (Derivation body Delta (graph1 (.projection 0) input input)) := projectionValue 0 xs
 have hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.work work input)) :=
   unaryValue InternalUnpair.left (.projection 0) work input xs (pairLeft input work results hstate) hi
 have hf : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.frame frame input)) :=
   unaryValue InternalListCodec.headCode OriginalHereditaryReturnStep.work frame work xs
     (InternalRawListRecursionSupportProof.consHead work frame rest hwork) hw
 have ht : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryReturnStep.frame) (numeral 1) input)) :=
   unaryValue InternalUnpair.left OriginalHereditaryReturnStep.frame (numeral 1) frame xs
     (pairLeft frame (numeral 1) payload hframe) hf
 apply InternalApplicationResultStackReturnSupportProof.nonzeroBranchIntro
   OriginalHereditaryReturnStep.work (.projection 0) _ out work xs hw
   (OriginalTypedDecoderInternalListProof.consNonzero work frame rest hwork)
 exact sameYesIntro (leftOf OriginalHereditaryReturnStep.frame) (OriginalRawSyntaxTransport.constant 1 1)
   _ (.projection 0) out (numeral 1) (numeral 1) xs ht (constantValue 1 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 1)))) hv

theorem restGraph (input work results frame rest : OTerm alpha)
 (hstate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hwork : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.rest rest input)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 have hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.work work input)) :=
   unaryValue InternalUnpair.left (.projection 0) work input xs (pairLeft input work results hstate) (projectionValue 0 xs)
 exact unaryValue InternalListCodec.tailCode OriginalHereditaryReturnStep.work rest work xs
   (InternalRawListRecursionSupportProof.consTail work frame rest hwork) hw

theorem popGraph (P : Program 1) (input rest value old stack out : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.rest rest input)))
 (hv : Nonempty (Derivation body Delta (graph1 P value input)))
 (ho : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.oldSuffix old input)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.pop P) out input)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 have hc := binaryValue InternalListCodec.consCode P OriginalHereditaryReturnStep.oldSuffix stack value old xs hs hv ho
 exact binaryValue InternalPairing.pairing OriginalHereditaryReturnStep.rest
   (consOf P OriginalHereditaryReturnStep.oldSuffix) out rest stack xs hp hr hc

theorem termRole (R : Program 2) (input out : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)))
 (hv : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.pop (OriginalHereditaryReturnStep.termValue R)) out input))) :
 Nonempty (Derivation body Delta (graph1
   (OriginalTypedDecoder.ifSame OriginalHereditaryReturnStep.role (OriginalRawSyntaxTransport.constant 1 0)
     (OriginalHereditaryReturnStep.pop (OriginalHereditaryReturnStep.termValue R))
     (OriginalTypedDecoder.ifSame OriginalHereditaryReturnStep.role (OriginalRawSyntaxTransport.constant 1 1)
       OriginalHereditaryReturnStep.listStep (.projection 0))) out input)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 exact sameYesIntro _ _ _ _ out (numeral 0) (numeral 0) xs hr (constantValue 0 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 0)))) hv

theorem listRole (R : Program 2) (input out : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 1) input)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.listStep out input))) :
 Nonempty (Derivation body Delta (graph1
   (OriginalTypedDecoder.ifSame OriginalHereditaryReturnStep.role (OriginalRawSyntaxTransport.constant 1 0)
     (OriginalHereditaryReturnStep.pop (OriginalHereditaryReturnStep.termValue R))
     (OriginalTypedDecoder.ifSame OriginalHereditaryReturnStep.role (OriginalRawSyntaxTransport.constant 1 1)
       OriginalHereditaryReturnStep.listStep (.projection 0))) out input)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 have h1 := sameYesIntro OriginalHereditaryReturnStep.role (OriginalRawSyntaxTransport.constant 1 1)
   OriginalHereditaryReturnStep.listStep (.projection 0) out (numeral 1) (numeral 1) xs hr (constantValue 1 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 1)))) hv
 exact sameNoIntro _ _ _ _ out (numeral 1) (numeral 0) xs hr (constantValue 0 xs) (numeralNe 1 0 (by decide)) h1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
