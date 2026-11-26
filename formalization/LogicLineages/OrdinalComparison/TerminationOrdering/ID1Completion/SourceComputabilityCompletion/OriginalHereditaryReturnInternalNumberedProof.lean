module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalNumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalHereditaryReturnInternalDispatchProof

theorem numberedLaw : OriginalHereditaryReturnInternalTargets.NumberedLaw := by
 intro body alpha Delta input first second typ raw payload number headTail head arityTail arityCode children baseRaw extrasRaw headObserved sortedBase observations headData typedData data out h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have v0 : Nonempty (Derivation body Delta (graph3 (OriginalRawSyntaxTransport.constant 3 5) (numeral 5) input first second)) :=
   constantValue 5 xs
 have v1 : Nonempty (Derivation body Delta (graph3 (.projection 0) input input first second)) :=
   projectionValue 0 xs
 have v2 : Nonempty (Derivation body Delta (graph3 (rightOf (.projection 0)) raw input first second)) :=
   unaryValue InternalUnpair.right (.projection 0) raw input xs (pairRight input typ raw h0) v1
 have v3 : Nonempty (Derivation body Delta (graph3 (rightOf (rightOf (.projection 0))) payload input first second)) :=
   unaryValue InternalUnpair.right (rightOf (.projection 0)) payload raw xs (pairRight raw (numeral 5) payload h1) v2
 have v4 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (rightOf (.projection 0)))) number input first second)) :=
   unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) number payload xs (pairLeft payload number headTail h2) v3
 have v5 : Nonempty (Derivation body Delta (graph3 (leftOf (.projection 0)) typ input first second)) :=
   unaryValue InternalUnpair.left (.projection 0) typ input xs (pairLeft input typ raw h0) v1
 have v6 : Nonempty (Derivation body Delta (graph3 (rightOf (rightOf (rightOf (.projection 0)))) headTail input first second)) :=
   unaryValue InternalUnpair.right (rightOf (rightOf (.projection 0))) headTail payload xs (pairRight payload number headTail h2) v3
 have v7 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (rightOf (rightOf (.projection 0))))) head input first second)) :=
   unaryValue InternalUnpair.left (rightOf (rightOf (rightOf (.projection 0)))) head headTail xs (pairLeft headTail head arityTail h3) v6
 have v8 : Nonempty (Derivation body Delta (graph3 (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) headObserved input first second)) :=
   unaryValue OriginalHeadClassNumber.classNumber (leftOf (rightOf (rightOf (rightOf (.projection 0))))) headObserved head xs h6 v7
 have v9 : Nonempty (Derivation body Delta (graph3 (.projection 1) first input first second)) :=
   projectionValue 1 xs
 have v10 : Nonempty (Derivation body Delta (graph3 (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) sortedBase input first second)) :=
   unaryValue OriginalNumericListSort.sort (.projection 1) sortedBase first xs h7 v9
 have v11 : Nonempty (Derivation body Delta (graph3 (.projection 2) second input first second)) :=
   projectionValue 2 xs
 have v12 : Nonempty (Derivation body Delta (graph3 (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2)) observations input first second)) :=
   binaryValue InternalPairing.pairing (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2) observations sortedBase second xs h8 v10 v11
 have v13 : Nonempty (Derivation body Delta (graph3 (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2))) headData input first second)) :=
   binaryValue InternalPairing.pairing (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2)) headData headObserved observations xs h9 v8 v12
 have v14 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2)))) typedData input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2))) typedData typ headData xs h10 v5 v13
 have v15 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2))))) data input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2)))) data number typedData xs h11 v4 v14
 have v16 : Nonempty (Derivation body Delta (graph3 (pairOf (OriginalRawSyntaxTransport.constant 3 5) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2)))))) out input first second)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 5) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2))))) out (numeral 5) data xs h12 v0 v15
 have v17 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (.projection 0))) (numeral 5) input first second)) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 5) raw xs (pairLeft raw (numeral 5) payload h1) v2
 exact dispatch5 input first second out v17 v16

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalNumberedProof
