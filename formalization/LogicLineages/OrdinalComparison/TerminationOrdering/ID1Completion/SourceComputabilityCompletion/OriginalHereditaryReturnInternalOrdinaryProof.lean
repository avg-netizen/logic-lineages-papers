module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalOrdinaryProof
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

theorem ordinaryLaw : OriginalHereditaryReturnInternalTargets.OrdinaryLaw := by
 intro body alpha Delta input first second typ raw payload head baseRaw headObserved sortedBase observations data out h0 h1 h2 h3 h4 h5 h6 h7
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have v0 : Nonempty (Derivation body Delta (graph3 (OriginalRawSyntaxTransport.constant 3 4) (numeral 4) input first second)) :=
   constantValue 4 xs
 have v1 : Nonempty (Derivation body Delta (graph3 (.projection 0) input input first second)) :=
   projectionValue 0 xs
 have v2 : Nonempty (Derivation body Delta (graph3 (leftOf (.projection 0)) typ input first second)) :=
   unaryValue InternalUnpair.left (.projection 0) typ input xs (pairLeft input typ raw h0) v1
 have v3 : Nonempty (Derivation body Delta (graph3 (rightOf (.projection 0)) raw input first second)) :=
   unaryValue InternalUnpair.right (.projection 0) raw input xs (pairRight input typ raw h0) v1
 have v4 : Nonempty (Derivation body Delta (graph3 (rightOf (rightOf (.projection 0))) payload input first second)) :=
   unaryValue InternalUnpair.right (rightOf (.projection 0)) payload raw xs (pairRight raw (numeral 4) payload h1) v3
 have v5 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (rightOf (.projection 0)))) head input first second)) :=
   unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) head payload xs (pairLeft payload head baseRaw h2) v4
 have v6 : Nonempty (Derivation body Delta (graph3 (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (.projection 0)))))) headObserved input first second)) :=
   unaryValue OriginalHeadClassNumber.classNumber (leftOf (rightOf (rightOf (.projection 0)))) headObserved head xs h3 v5
 have v7 : Nonempty (Derivation body Delta (graph3 (.projection 1) first input first second)) :=
   projectionValue 1 xs
 have v8 : Nonempty (Derivation body Delta (graph3 (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) sortedBase input first second)) :=
   unaryValue OriginalNumericListSort.sort (.projection 1) sortedBase first xs h4 v7
 have v9 : Nonempty (Derivation body Delta (graph3 (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (.projection 0)))))) (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1)))) observations input first second)) :=
   binaryValue InternalPairing.pairing (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (.projection 0)))))) (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) observations headObserved sortedBase xs h5 v6 v8
 have v10 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (.projection 0)))))) (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))))) data input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (.projection 0)))))) (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1)))) data typ observations xs h6 v2 v9
 have v11 : Nonempty (Derivation body Delta (graph3 (pairOf (OriginalRawSyntaxTransport.constant 3 4) (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (.projection 0)))))) (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1)))))) out input first second)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 4) (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (.projection 0)))))) (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))))) out (numeral 4) data xs h7 v0 v10
 have v12 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (.projection 0))) (numeral 4) input first second)) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 4) raw xs (pairLeft raw (numeral 4) payload h1) v3
 exact dispatch4 input first second out v12 v11

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalOrdinaryProof
