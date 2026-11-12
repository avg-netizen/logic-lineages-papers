module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListNilProof
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
theorem listNilLaw : OriginalHereditaryReturnStepInternalTargets.ListNilLaw := by
 intro R body alpha Delta input work results frame rest payload raw rawPayload old stack out
   hstate hwork hframe hrole hraw htag hold hstack hout
 let xs : Fin 1 → OTerm alpha := ![input]
 have ht : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryReturnStep.raw) (numeral 6) input)) :=
   unaryValue InternalUnpair.left OriginalHereditaryReturnStep.raw (numeral 6) raw xs (pairLeft raw (numeral 6) rawPayload htag) hraw
 have hp := popGraph (OriginalRawSyntaxTransport.constant 1 0) input rest (numeral 0) old stack out
   (restGraph input work results frame rest hstate hwork) (constantValue 0 xs) hold hstack hout
 have hy := sameYesIntro (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 6)
   (OriginalHereditaryReturnStep.pop (OriginalRawSyntaxTransport.constant 1 0))
   (OriginalTypedDecoder.ifSame (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 7)
     (OriginalHereditaryReturnStep.pop OriginalHereditaryReturnStep.argumentsValue) (.projection 0)) out (numeral 6) (numeral 6) xs ht (constantValue 6 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 6)))) hp
 exact control R input work results frame rest payload out hstate hwork hframe (listRole R input out hrole hy)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListNilProof
