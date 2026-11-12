module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalApplicationProof
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

theorem applicationLaw : OriginalHereditaryReturnInternalTargets.ApplicationLaw := by
 intro body alpha Delta input first second typ raw payload domain children fnRaw argRaw fnType fnObserved argObserved observations typedData data out h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have v0 : Nonempty (Derivation body Delta (graph3 (OriginalRawSyntaxTransport.constant 3 2) (numeral 2) input first second)) :=
   constantValue 2 xs
 have v1 : Nonempty (Derivation body Delta (graph3 (.projection 0) input input first second)) :=
   projectionValue 0 xs
 have v2 : Nonempty (Derivation body Delta (graph3 (rightOf (.projection 0)) raw input first second)) :=
   unaryValue InternalUnpair.right (.projection 0) raw input xs (pairRight input typ raw h0) v1
 have v3 : Nonempty (Derivation body Delta (graph3 (rightOf (rightOf (.projection 0))) payload input first second)) :=
   unaryValue InternalUnpair.right (rightOf (.projection 0)) payload raw xs (pairRight raw (numeral 2) payload h1) v2
 have v4 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (rightOf (.projection 0)))) domain input first second)) :=
   unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) domain payload xs (pairLeft payload domain children h2) v3
 have v5 : Nonempty (Derivation body Delta (graph3 (leftOf (.projection 0)) typ input first second)) :=
   unaryValue InternalUnpair.left (.projection 0) typ input xs (pairLeft input typ raw h0) v1
 have v6 : Nonempty (Derivation body Delta (graph3 (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) fnType input first second)) :=
   binaryValue InternalListCodec.consCode (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0)) fnType domain typ xs h4 v4 v5
 have v7 : Nonempty (Derivation body Delta (graph3 (.projection 1) first input first second)) :=
   projectionValue 1 xs
 have v8 : Nonempty (Derivation body Delta (graph3 (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) fnObserved input first second)) :=
   binaryValue InternalPairing.pairing (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1) fnObserved fnType first xs h5 v6 v7
 have v9 : Nonempty (Derivation body Delta (graph3 (.projection 2) second input first second)) :=
   projectionValue 2 xs
 have v10 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2)) argObserved input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2) argObserved domain second xs h6 v4 v9
 have v11 : Nonempty (Derivation body Delta (graph3 (pairOf (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2))) observations input first second)) :=
   binaryValue InternalPairing.pairing (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2)) observations fnObserved argObserved xs h7 v8 v10
 have v12 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (.projection 0)) (pairOf (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2)))) typedData input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (.projection 0)) (pairOf (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2))) typedData typ observations xs h8 v5 v11
 have v13 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2))))) data input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2)))) data domain typedData xs h9 v4 v12
 have v14 : Nonempty (Derivation body Delta (graph3 (pairOf (OriginalRawSyntaxTransport.constant 3 2) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2)))))) out input first second)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 2) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2))))) out (numeral 2) data xs h10 v0 v13
 have v15 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (.projection 0))) (numeral 2) input first second)) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 2) raw xs (pairLeft raw (numeral 2) payload h1) v2
 exact dispatch2 input first second out v15 v14

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalApplicationProof
