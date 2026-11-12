module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalLambdaProof
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

theorem lambdaLaw : OriginalHereditaryReturnInternalTargets.LambdaLaw := by
 intro body alpha Delta input first second typ raw payload domain childRaw codomain observed typedData data out h0 h1 h2 h3 h4 h5 h6 h7
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have v0 : Nonempty (Derivation body Delta (graph3 (OriginalRawSyntaxTransport.constant 3 1) (numeral 1) input first second)) :=
   constantValue 1 xs
 have v1 : Nonempty (Derivation body Delta (graph3 (.projection 0) input input first second)) :=
   projectionValue 0 xs
 have v2 : Nonempty (Derivation body Delta (graph3 (rightOf (.projection 0)) raw input first second)) :=
   unaryValue InternalUnpair.right (.projection 0) raw input xs (pairRight input typ raw h0) v1
 have v3 : Nonempty (Derivation body Delta (graph3 (rightOf (rightOf (.projection 0))) payload input first second)) :=
   unaryValue InternalUnpair.right (rightOf (.projection 0)) payload raw xs (pairRight raw (numeral 1) payload h1) v2
 have v4 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (rightOf (.projection 0)))) domain input first second)) :=
   unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) domain payload xs (pairLeft payload domain childRaw h2) v3
 have v5 : Nonempty (Derivation body Delta (graph3 (leftOf (.projection 0)) typ input first second)) :=
   unaryValue InternalUnpair.left (.projection 0) typ input xs (pairLeft input typ raw h0) v1
 have v6 : Nonempty (Derivation body Delta (graph3 (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) codomain input first second)) :=
   unaryValue InternalListCodec.tailCode (leftOf (.projection 0)) codomain typ xs (InternalRawListRecursionSupportProof.consTail typ domain codomain h3) v5
 have v7 : Nonempty (Derivation body Delta (graph3 (.projection 1) first input first second)) :=
   projectionValue 1 xs
 have v8 : Nonempty (Derivation body Delta (graph3 (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1)) observed input first second)) :=
   binaryValue InternalPairing.pairing (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1) observed codomain first xs h4 v6 v7
 have v9 : Nonempty (Derivation body Delta (graph3 (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1))) typedData input first second)) :=
   binaryValue InternalPairing.pairing (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1)) typedData codomain observed xs h5 v6 v8
 have v10 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1)))) data input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1))) data domain typedData xs h6 v4 v9
 have v11 : Nonempty (Derivation body Delta (graph3 (pairOf (OriginalRawSyntaxTransport.constant 3 1) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1))))) out input first second)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 1) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1)))) out (numeral 1) data xs h7 v0 v10
 have v12 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (.projection 0))) (numeral 1) input first second)) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 1) raw xs (pairLeft raw (numeral 1) payload h1) v2
 exact dispatch1 input first second out v12 v11

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalLambdaProof
