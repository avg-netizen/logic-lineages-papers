module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalProof
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
open OriginalRootObservationInternalSupportProof

theorem variableLaw : OriginalRootObservationInternalTargets.VariableLaw := by
 intro R body alpha Delta input parameter typ raw index data out h0 h1 h2 h3
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have v0 : Nonempty (Derivation body Delta (graph2 (.projection 0) input input parameter)) :=
   projectionValue 0 xs
 have v1 : Nonempty (Derivation body Delta (graph2 (.projection 1) parameter input parameter)) :=
   projectionValue 1 xs
 have v2 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType typ input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.packed typ input xs (pairLeft input typ raw h0) v0
 have v3 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.raw raw input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.packed raw input xs (pairRight input typ raw h0) v0
 have v4 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 0) input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.raw (numeral 0) raw xs (pairLeft raw (numeral 0) index h1) v3
 have v5 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.payload index input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.raw index raw xs (pairRight raw (numeral 0) index h1) v3
 have v6 : Nonempty (Derivation body Delta (graph2 (pairOf OriginalRootObservation.resultType OriginalRootObservation.payload) data input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.resultType OriginalRootObservation.payload data typ index xs h2 v2 v5
 have v7 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.constant 2 0) (numeral 0) input parameter)) :=
   constantValue 0 xs
 have v8 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.variableCase out input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (pairOf OriginalRootObservation.resultType OriginalRootObservation.payload) out (numeral 0) data xs h3 v7 v6
 exact dispatch0 R input parameter out v4 v8

theorem bottomLaw : OriginalRootObservationInternalTargets.BottomLaw := by
 intro R body alpha Delta input parameter typ raw out h0 h1 h2
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have v0 : Nonempty (Derivation body Delta (graph2 (.projection 0) input input parameter)) :=
   projectionValue 0 xs
 have v1 : Nonempty (Derivation body Delta (graph2 (.projection 1) parameter input parameter)) :=
   projectionValue 1 xs
 have v2 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType typ input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.packed typ input xs (pairLeft input typ raw h0) v0
 have v3 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.raw raw input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.packed raw input xs (pairRight input typ raw h0) v0
 have v4 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 3) input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.raw (numeral 3) raw xs (pairLeft raw (numeral 3) typ h1) v3
 have v5 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.payload typ input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.raw typ raw xs (pairRight raw (numeral 3) typ h1) v3
 have v6 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.constant 2 3) (numeral 3) input parameter)) :=
   constantValue 3 xs
 have v7 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bottom out input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 3) OriginalRootObservation.resultType out (numeral 3) typ xs h2 v6 v2
 exact dispatch3 R input parameter out v4 v7

theorem applicationLaw : OriginalRootObservationInternalTargets.ApplicationLaw := by
 intro R body alpha Delta input parameter typ raw domain children payload fnRaw argRaw fnType fnPacked argPacked fnValue argValue fnObserved argObserved observations typedData data out h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have v0 : Nonempty (Derivation body Delta (graph2 (.projection 0) input input parameter)) :=
   projectionValue 0 xs
 have v1 : Nonempty (Derivation body Delta (graph2 (.projection 1) parameter input parameter)) :=
   projectionValue 1 xs
 have v2 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType typ input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.packed typ input xs (pairLeft input typ raw h0) v0
 have v3 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.raw raw input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.packed raw input xs (pairRight input typ raw h0) v0
 have v4 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.raw (numeral 2) raw xs (pairLeft raw (numeral 2) payload h1) v3
 have v5 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.payload payload input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.raw payload raw xs (pairRight raw (numeral 2) payload h1) v3
 have v6 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain domain input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.payload domain payload xs (pairLeft payload domain children h2) v5
 have v7 : Nonempty (Derivation body Delta (graph2 (rightOf OriginalRootObservation.payload) children input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.payload children payload xs (pairRight payload domain children h2) v5
 have v8 : Nonempty (Derivation body Delta (graph2 (leftOf (rightOf OriginalRootObservation.payload)) fnRaw input parameter)) :=
   unaryValue InternalUnpair.left (rightOf OriginalRootObservation.payload) fnRaw children xs (pairLeft children fnRaw argRaw h3) v7
 have v9 : Nonempty (Derivation body Delta (graph2 (rightOf (rightOf OriginalRootObservation.payload)) argRaw input parameter)) :=
   unaryValue InternalUnpair.right (rightOf OriginalRootObservation.payload) argRaw children xs (pairRight children fnRaw argRaw h3) v7
 have v10 : Nonempty (Derivation body Delta (graph2 (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) fnType input parameter)) :=
   binaryValue InternalListCodec.consCode OriginalRootObservation.domain OriginalRootObservation.resultType fnType domain typ xs h4 v6 v2
 have v11 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.functionPacked fnPacked input parameter)) :=
   binaryValue InternalPairing.pairing (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) (leftOf (rightOf OriginalRootObservation.payload)) fnPacked fnType fnRaw xs h5 v10 v8
 have v12 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.argumentPacked argPacked input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.domain (rightOf (rightOf OriginalRootObservation.payload)) argPacked domain argRaw xs h6 v6 v9
 have v13 : Nonempty (Derivation body Delta (graph2 (.composition R ![OriginalRootObservation.functionPacked,OriginalRootObservation.parameter]) fnValue input parameter)) :=
   binaryValue R OriginalRootObservation.functionPacked OriginalRootObservation.parameter fnValue fnPacked parameter xs h7 v11 v1
 have v14 : Nonempty (Derivation body Delta (graph2 (.composition R ![OriginalRootObservation.argumentPacked,OriginalRootObservation.parameter]) argValue input parameter)) :=
   binaryValue R OriginalRootObservation.argumentPacked OriginalRootObservation.parameter argValue argPacked parameter xs h8 v12 v1
 have v15 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.typed R (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) OriginalRootObservation.functionPacked OriginalRootObservation.parameter) fnObserved input parameter)) :=
   binaryValue InternalPairing.pairing (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) (.composition R ![OriginalRootObservation.functionPacked,OriginalRootObservation.parameter]) fnObserved fnType fnValue xs h9 v10 v13
 have v16 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.typed R OriginalRootObservation.domain OriginalRootObservation.argumentPacked OriginalRootObservation.parameter) argObserved input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.domain (.composition R ![OriginalRootObservation.argumentPacked,OriginalRootObservation.parameter]) argObserved domain argValue xs h10 v6 v14
 have v17 : Nonempty (Derivation body Delta (graph2 (pairOf (OriginalRootObservation.typed R (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) OriginalRootObservation.functionPacked OriginalRootObservation.parameter) (OriginalRootObservation.typed R OriginalRootObservation.domain OriginalRootObservation.argumentPacked OriginalRootObservation.parameter)) observations input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRootObservation.typed R (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) OriginalRootObservation.functionPacked OriginalRootObservation.parameter) (OriginalRootObservation.typed R OriginalRootObservation.domain OriginalRootObservation.argumentPacked OriginalRootObservation.parameter) observations fnObserved argObserved xs h11 v15 v16
 have v18 : Nonempty (Derivation body Delta (graph2 (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.typed R (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) OriginalRootObservation.functionPacked OriginalRootObservation.parameter) (OriginalRootObservation.typed R OriginalRootObservation.domain OriginalRootObservation.argumentPacked OriginalRootObservation.parameter))) typedData input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.resultType (pairOf (OriginalRootObservation.typed R (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) OriginalRootObservation.functionPacked OriginalRootObservation.parameter) (OriginalRootObservation.typed R OriginalRootObservation.domain OriginalRootObservation.argumentPacked OriginalRootObservation.parameter)) typedData typ observations xs h12 v2 v17
 have v19 : Nonempty (Derivation body Delta (graph2 (pairOf OriginalRootObservation.domain (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.typed R (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) OriginalRootObservation.functionPacked OriginalRootObservation.parameter) (OriginalRootObservation.typed R OriginalRootObservation.domain OriginalRootObservation.argumentPacked OriginalRootObservation.parameter)))) data input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.domain (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.typed R (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) OriginalRootObservation.functionPacked OriginalRootObservation.parameter) (OriginalRootObservation.typed R OriginalRootObservation.domain OriginalRootObservation.argumentPacked OriginalRootObservation.parameter))) data domain typedData xs h13 v6 v18
 have v20 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.constant 2 2) (numeral 2) input parameter)) :=
   constantValue 2 xs
 have v21 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.application R) out input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 2) (pairOf OriginalRootObservation.domain (pairOf OriginalRootObservation.resultType (pairOf (OriginalRootObservation.typed R (consOf OriginalRootObservation.domain OriginalRootObservation.resultType) OriginalRootObservation.functionPacked OriginalRootObservation.parameter) (OriginalRootObservation.typed R OriginalRootObservation.domain OriginalRootObservation.argumentPacked OriginalRootObservation.parameter)))) out (numeral 2) data xs h14 v20 v19
 exact dispatch2 R input parameter out v4 v21

theorem lambdaLaw : OriginalRootObservationInternalTargets.LambdaLaw := by
 intro R body alpha Delta input parameter arrow raw domain codomain payload childRaw childPacked context gamma extended childParam childValue observed typedData data out h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have v0 : Nonempty (Derivation body Delta (graph2 (.projection 0) input input parameter)) :=
   projectionValue 0 xs
 have v1 : Nonempty (Derivation body Delta (graph2 (.projection 1) parameter input parameter)) :=
   projectionValue 1 xs
 have v2 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType arrow input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.packed arrow input xs (pairLeft input arrow raw h0) v0
 have v3 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.raw raw input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.packed raw input xs (pairRight input arrow raw h0) v0
 have v4 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.raw (numeral 1) raw xs (pairLeft raw (numeral 1) payload h1) v3
 have v5 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.payload payload input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.raw payload raw xs (pairRight raw (numeral 1) payload h1) v3
 have v6 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain domain input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.payload domain payload xs (pairLeft payload domain childRaw h2) v5
 have v7 : Nonempty (Derivation body Delta (graph2 (rightOf OriginalRootObservation.payload) childRaw input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.payload childRaw payload xs (pairRight payload domain childRaw h2) v5
 have v8 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.codomain codomain input parameter)) :=
   unaryValue InternalListCodec.tailCode OriginalRootObservation.resultType codomain arrow xs (InternalRawListRecursionSupportProof.consTail arrow domain codomain h3) v2
 have v9 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bodyPacked childPacked input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.codomain (rightOf OriginalRootObservation.payload) childPacked codomain childRaw xs h4 v8 v7
 have v10 : Nonempty (Derivation body Delta (graph2 (leftOf OriginalRootObservation.parameter) context input parameter)) :=
   unaryValue InternalUnpair.left OriginalRootObservation.parameter context parameter xs (pairLeft parameter context gamma h5) v1
 have v11 : Nonempty (Derivation body Delta (graph2 (rightOf OriginalRootObservation.parameter) gamma input parameter)) :=
   unaryValue InternalUnpair.right OriginalRootObservation.parameter gamma parameter xs (pairRight parameter context gamma h5) v1
 have v12 : Nonempty (Derivation body Delta (graph2 (consOf OriginalRootObservation.domain (rightOf OriginalRootObservation.parameter)) extended input parameter)) :=
   binaryValue InternalListCodec.consCode OriginalRootObservation.domain (rightOf OriginalRootObservation.parameter) extended domain gamma xs h6 v6 v11
 have v13 : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter childParam input parameter)) :=
   binaryValue InternalPairing.pairing (leftOf OriginalRootObservation.parameter) (consOf OriginalRootObservation.domain (rightOf OriginalRootObservation.parameter)) childParam context extended xs h7 v10 v12
 have v14 : Nonempty (Derivation body Delta (graph2 (.composition R ![OriginalRootObservation.bodyPacked,OriginalRootObservation.childParameter]) childValue input parameter)) :=
   binaryValue R OriginalRootObservation.bodyPacked OriginalRootObservation.childParameter childValue childPacked childParam xs h8 v9 v13
 have v15 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.typed R OriginalRootObservation.codomain OriginalRootObservation.bodyPacked OriginalRootObservation.childParameter) observed input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.codomain (.composition R ![OriginalRootObservation.bodyPacked,OriginalRootObservation.childParameter]) observed codomain childValue xs h9 v8 v14
 have v16 : Nonempty (Derivation body Delta (graph2 (pairOf OriginalRootObservation.codomain (OriginalRootObservation.typed R OriginalRootObservation.codomain OriginalRootObservation.bodyPacked OriginalRootObservation.childParameter)) typedData input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.codomain (OriginalRootObservation.typed R OriginalRootObservation.codomain OriginalRootObservation.bodyPacked OriginalRootObservation.childParameter) typedData codomain observed xs h10 v8 v15
 have v17 : Nonempty (Derivation body Delta (graph2 (pairOf OriginalRootObservation.domain (pairOf OriginalRootObservation.codomain (OriginalRootObservation.typed R OriginalRootObservation.codomain OriginalRootObservation.bodyPacked OriginalRootObservation.childParameter))) data input parameter)) :=
   binaryValue InternalPairing.pairing OriginalRootObservation.domain (pairOf OriginalRootObservation.codomain (OriginalRootObservation.typed R OriginalRootObservation.codomain OriginalRootObservation.bodyPacked OriginalRootObservation.childParameter)) data domain typedData xs h11 v6 v16
 have v18 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.constant 2 1) (numeral 1) input parameter)) :=
   constantValue 1 xs
 have v19 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.lambda R) out input parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 1) (pairOf OriginalRootObservation.domain (pairOf OriginalRootObservation.codomain (OriginalRootObservation.typed R OriginalRootObservation.codomain OriginalRootObservation.bodyPacked OriginalRootObservation.childParameter))) out (numeral 1) data xs h12 v18 v17
 exact dispatch1 R input parameter out v4 v19
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalProof
