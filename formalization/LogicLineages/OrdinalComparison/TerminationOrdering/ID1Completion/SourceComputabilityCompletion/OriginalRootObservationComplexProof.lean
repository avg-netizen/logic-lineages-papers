module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexProof
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
open OriginalRootObservationComplexSupportProof

theorem ordinaryLaw : OriginalRootObservationComplexTargets.OrdinaryLaw := by
 intro R body alpha Delta input parameter typ raw payload head base headValue baseValues sortedBase headAndBase data out h0 h1 h2 h3 h4 h5 h6 h7 h8
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have v0 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.packed input input parameter)) :=
   projectionValue 0 xs
 have v1 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.parameter parameter input parameter)) :=
   projectionValue 1 xs
 have v2 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType typ input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.packed typ input xs (pairLeft input typ raw h0) v0
 have v3 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.raw raw input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.packed raw input xs (pairRight input typ raw h0) v0
 have v4 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 4) input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.raw (numeral 4) raw xs (pairLeft raw (numeral 4) payload h1) v3
 have v5 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.payload payload input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.raw payload raw xs (pairRight raw (numeral 4) payload h1) v3
 have v6 : Nonempty (Derivation body Delta (graph2 (leftOf OriginalRootObservation.payload) head input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.payload head payload xs (pairLeft payload head base h2) v5
 have v7 : Nonempty (Derivation body Delta (graph2 (rightOf OriginalRootObservation.payload) base input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.payload base payload xs (pairRight payload head base h2) v5
 have v8 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.headClass (leftOf OriginalRootObservation.payload)) headValue input parameter)) :=
   unaryValue OriginalHeadClassNumber.classNumber (leftOf OriginalRootObservation.payload) headValue head xs h3 v6
 have v9 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.arguments R (rightOf OriginalRootObservation.payload)) baseValues input parameter)) :=
   binaryValue (OriginalTypedArgumentObservations.argumentObservations R) (rightOf OriginalRootObservation.payload) OriginalRootObservation.parameter baseValues base parameter xs h4 v7 v1
 have v10 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.sortedArguments R (rightOf OriginalRootObservation.payload)) sortedBase input parameter)) :=
   unaryValue OriginalNumericListSort.sort (OriginalRootObservation.arguments R (rightOf OriginalRootObservation.payload)) sortedBase baseValues xs h5 v9
 have v11 : Nonempty (Derivation body Delta (graph2 (pairOf (OriginalRootObservation.headClass (leftOf OriginalRootObservation.payload)) (OriginalRootObservation.sortedArguments R (rightOf OriginalRootObservation.payload))) headAndBase input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRootObservation.headClass (leftOf OriginalRootObservation.payload)) (OriginalRootObservation.sortedArguments R (rightOf OriginalRootObservation.payload)) headAndBase headValue sortedBase xs h6 v8 v10
 have v12 : Nonempty (Derivation body Delta (graph2 (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.headClass (leftOf OriginalRootObservation.payload)) (OriginalRootObservation.sortedArguments R (rightOf OriginalRootObservation.payload)))) data input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.resultType (pairOf (OriginalRootObservation.headClass (leftOf OriginalRootObservation.payload)) (OriginalRootObservation.sortedArguments R (rightOf OriginalRootObservation.payload))) data typ headAndBase xs h7 v2 v11
 have v13 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.constant 2 4) (numeral 4) input parameter)) :=
   constantValue 4 xs
 have v14 : Nonempty (Derivation body Delta (graph2 (ordinary R) out input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 4) (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.headClass (leftOf OriginalRootObservation.payload)) (OriginalRootObservation.sortedArguments R (rightOf OriginalRootObservation.payload)))) out (numeral 4) data xs h8 v13 v12
 exact dispatch4 R input parameter out v4 v14

theorem numberedLaw : OriginalRootObservationComplexTargets.NumberedLaw := by
 intro R body alpha Delta input parameter typ raw payload label afterLabel head afterHead encodedType numberedFields base afterBase extraTypes extras headValue baseValues sortedBase extraValues baseAndExtras headAndArgs typedData data out h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have v0 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.packed input input parameter)) :=
   projectionValue 0 xs
 have v1 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.parameter parameter input parameter)) :=
   projectionValue 1 xs
 have v2 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType typ input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.packed typ input xs (pairLeft input typ raw h0) v0
 have v3 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.raw raw input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.packed raw input xs (pairRight input typ raw h0) v0
 have v4 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 5) input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.raw (numeral 5) raw xs (pairLeft raw (numeral 5) payload h1) v3
 have v5 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.payload payload input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.raw payload raw xs (pairRight raw (numeral 5) payload h1) v3
 have v6 : Nonempty (Derivation body Delta (graph2 (leftOf OriginalRootObservation.payload) label input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.payload label payload xs (pairLeft payload label afterLabel h2) v5
 have v7 : Nonempty (Derivation body Delta (graph2 (rightOf OriginalRootObservation.payload) afterLabel input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.payload afterLabel payload xs (pairRight payload label afterLabel h2) v5
 have v8 : Nonempty (Derivation body Delta (graph2 (leftOf (rightOf OriginalRootObservation.payload)) head input parameter)) :=
   unaryValue InternalUnpair.left (rightOf OriginalRootObservation.payload) head afterLabel xs (pairLeft afterLabel head afterHead h3) v7
 have v9 : Nonempty (Derivation body Delta (graph2 (rightOf (rightOf OriginalRootObservation.payload)) afterHead input parameter)) :=
   unaryValue InternalUnpair.right (rightOf OriginalRootObservation.payload) afterHead afterLabel xs (pairRight afterLabel head afterHead h3) v7
 have v10 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.numberedTail numberedFields input parameter)) :=
   unaryValue InternalUnpair.right (rightOf (rightOf OriginalRootObservation.payload)) numberedFields afterHead xs (pairRight afterHead encodedType numberedFields h4) v9
 have v11 : Nonempty (Derivation body Delta (graph2 (leftOf OriginalRootObservation.numberedTail) base input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.numberedTail base numberedFields xs (pairLeft numberedFields base afterBase h5) v10
 have v12 : Nonempty (Derivation body Delta (graph2 (rightOf OriginalRootObservation.numberedTail) afterBase input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.numberedTail afterBase numberedFields xs (pairRight numberedFields base afterBase h5) v10
 have v13 : Nonempty (Derivation body Delta (graph2 (rightOf (rightOf OriginalRootObservation.numberedTail)) extras input parameter)) :=
   unaryValue InternalUnpair.right (rightOf OriginalRootObservation.numberedTail) extras afterBase xs (pairRight afterBase extraTypes extras h6) v12
 have v14 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.headClass (leftOf (rightOf OriginalRootObservation.payload))) headValue input parameter)) :=
   unaryValue OriginalHeadClassNumber.classNumber (leftOf (rightOf OriginalRootObservation.payload)) headValue head xs h7 v8
 have v15 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.arguments R (leftOf OriginalRootObservation.numberedTail)) baseValues input parameter)) :=
   binaryValue (OriginalTypedArgumentObservations.argumentObservations R) (leftOf OriginalRootObservation.numberedTail) OriginalRootObservation.parameter baseValues base parameter xs h8 v11 v1
 have v16 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) sortedBase input parameter)) :=
   unaryValue OriginalNumericListSort.sort (OriginalRootObservation.arguments R (leftOf OriginalRootObservation.numberedTail)) sortedBase baseValues xs h9 v15
 have v17 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail))) extraValues input parameter)) :=
   binaryValue (OriginalTypedArgumentObservations.argumentObservations R) (rightOf (rightOf OriginalRootObservation.numberedTail)) OriginalRootObservation.parameter extraValues extras parameter xs h10 v13 v1
 have v18 : Nonempty (Derivation body Delta (graph2 (pairOf (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail)))) baseAndExtras input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail))) baseAndExtras sortedBase extraValues xs h11 v16 v17
 have v19 : Nonempty (Derivation body Delta (graph2 (pairOf (OriginalRootObservation.headClass (leftOf (rightOf OriginalRootObservation.payload))) (pairOf (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail))))) headAndArgs input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRootObservation.headClass (leftOf (rightOf OriginalRootObservation.payload))) (pairOf (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail)))) headAndArgs headValue baseAndExtras xs h12 v14 v18
 have v20 : Nonempty (Derivation body Delta (graph2 (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.headClass (leftOf (rightOf OriginalRootObservation.payload))) (pairOf (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail)))))) typedData input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.resultType (pairOf (OriginalRootObservation.headClass (leftOf (rightOf OriginalRootObservation.payload))) (pairOf (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail))))) typedData typ headAndArgs xs h13 v2 v19
 have v21 : Nonempty (Derivation body Delta (graph2 (pairOf (leftOf OriginalRootObservation.payload) (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.headClass (leftOf (rightOf OriginalRootObservation.payload))) (pairOf (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail))))))) data input parameter)) :=
   binaryValue InternalPairing.pairing (leftOf OriginalRootObservation.payload) (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.headClass (leftOf (rightOf OriginalRootObservation.payload))) (pairOf (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail)))))) data label typedData xs h14 v6 v20
 have v22 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.constant 2 5) (numeral 5) input parameter)) :=
   constantValue 5 xs
 have v23 : Nonempty (Derivation body Delta (graph2 (numbered R) out input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 5) (pairOf (leftOf OriginalRootObservation.payload) (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.headClass (leftOf (rightOf OriginalRootObservation.payload))) (pairOf (OriginalRootObservation.sortedArguments R (leftOf OriginalRootObservation.numberedTail)) (OriginalRootObservation.arguments R (rightOf (rightOf OriginalRootObservation.numberedTail))))))) out (numeral 5) data xs h15 v22 v21
 exact dispatch5 R input parameter out v4 v23
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexProof
