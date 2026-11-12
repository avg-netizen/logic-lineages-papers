module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
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

theorem dispatch0 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 0) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 variableCase out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have h0 := sameYesIntro tag (OriginalRawSyntaxTransport.constant 2 0) variableCase (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))))
   out (numeral 0) (numeral 0) xs ht (constantValue 0 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 0)))) hv
 exact h0

theorem dispatch1 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (lambda R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have h1 := sameYesIntro tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))))
   out (numeral 1) (numeral 1) xs ht (constantValue 1 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 1)))) hv
 have h0 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 0) variableCase (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))))
   out (numeral 1) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 1 0 (by decide)) h1
 exact h0

theorem dispatch2 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 2) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.application R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have h2 := sameYesIntro tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))
   out (numeral 2) (numeral 2) xs ht (constantValue 2 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 2)))) hv
 have h1 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))))
   out (numeral 2) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 2 1 (by decide)) h2
 have h0 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 0) variableCase (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))))
   out (numeral 2) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 2 0 (by decide)) h1
 exact h0

theorem dispatch3 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 3) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 bottom out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have h3 := sameYesIntro tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))
   out (numeral 3) (numeral 3) xs ht (constantValue 3 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 3)))) hv
 have h2 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))
   out (numeral 3) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 3 2 (by decide)) h3
 have h1 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))))
   out (numeral 3) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 3 1 (by decide)) h2
 have h0 := sameNoIntro tag (OriginalRawSyntaxTransport.constant 2 0) variableCase (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (OriginalRootObservation.application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))))
   out (numeral 3) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 3 0 (by decide)) h1
 exact h0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
