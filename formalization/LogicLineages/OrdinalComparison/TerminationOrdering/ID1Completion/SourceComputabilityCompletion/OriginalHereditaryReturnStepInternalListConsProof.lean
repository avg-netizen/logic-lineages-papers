module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListConsProof
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
open OriginalHereditaryReturnStepInternalSupportProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
theorem listConsLaw : OriginalHereditaryReturnStepInternalTargets.ListConsLaw := by
 intro R body alpha Delta input work results frame rest payload raw rawPayload first second old value stack out
   hstate hwork hframe hrole hraw htag hfirst hsecond hold hvalue hstack hout
 let xs : Fin 1 → OTerm alpha := ![input]
 have ht : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryReturnStep.raw) (numeral 7) input)) :=
   unaryValue InternalUnpair.left OriginalHereditaryReturnStep.raw (numeral 7) raw xs (pairLeft raw (numeral 7) rawPayload htag) hraw
 have hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.argumentsValue value input)) :=
   ternaryValue OriginalHereditaryReturn.returnArgumentsCons OriginalHereditaryReturnStep.raw
     OriginalHereditaryReturnStep.firstSlot OriginalHereditaryReturnStep.secondSlot value raw first second xs hvalue hraw hfirst hsecond
 have hp := popGraph OriginalHereditaryReturnStep.argumentsValue input rest value old stack out
   (restGraph input work results frame rest hstate hwork) hv hold hstack hout
 have hy := sameYesIntro (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 7)
   (OriginalHereditaryReturnStep.pop OriginalHereditaryReturnStep.argumentsValue) (.projection 0) out (numeral 7) (numeral 7) xs ht (constantValue 7 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 7)))) hp
 have hz : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.listStep out input)) :=
   sameNoIntro (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 6)
     (OriginalHereditaryReturnStep.pop (OriginalRawSyntaxTransport.constant 1 0)) _ out (numeral 7) (numeral 6) xs ht
     (constantValue 6 xs) (numeralNe 7 6 (by decide)) hy
 exact control R input work results frame rest payload out hstate hwork hframe (listRole R input out hrole hz)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListConsProof
