module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRootObservation
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem dispatch4 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 4) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (ordinary R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have h4 := sameYesIntro tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))
   out (numeral 4) (numeral 4) xs ht (constantValue 4 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 4)))) hv
 have h3 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))
   out (numeral 4) (numeral 3) xs ht (constantValue 3 xs) (numeralNe 4 3 (by decide)) h4
 have h2 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))
   out (numeral 4) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 4 2 (by decide)) h3
 have h1 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))))
   out (numeral 4) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 4 1 (by decide)) h2
 have h0 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 0) variableCase (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))))
   out (numeral 4) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 4 0 (by decide)) h1
 exact h0

theorem dispatch5 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 5) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (numbered R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have h5 := sameYesIntro tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)
   out (numeral 5) (numeral 5) xs ht (constantValue 5 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 5)))) hv
 have h4 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))
   out (numeral 5) (numeral 4) xs ht (constantValue 4 xs) (numeralNe 5 4 (by decide)) h5
 have h3 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))
   out (numeral 5) (numeral 3) xs ht (constantValue 3 xs) (numeralNe 5 3 (by decide)) h4
 have h2 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))
   out (numeral 5) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 5 2 (by decide)) h3
 have h1 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))))
   out (numeral 5) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 5 1 (by decide)) h2
 have h0 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 0) variableCase (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))))
   out (numeral 5) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 5 0 (by decide)) h1
 exact h0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexSupportProof
