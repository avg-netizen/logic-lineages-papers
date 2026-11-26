module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalVariableProof
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

theorem variableLaw : OriginalHereditaryReturnInternalTargets.VariableLaw := by
 intro body alpha Delta input first second typ raw index data out h0 h1 h2 h3
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have v0 : Nonempty (Derivation body Delta (graph3 (OriginalRawSyntaxTransport.constant 3 0) (numeral 0) input first second)) :=
   constantValue 0 xs
 have v1 : Nonempty (Derivation body Delta (graph3 (.projection 0) input input first second)) :=
   projectionValue 0 xs
 have v2 : Nonempty (Derivation body Delta (graph3 (leftOf (.projection 0)) typ input first second)) :=
   unaryValue InternalUnpair.left (.projection 0) typ input xs (pairLeft input typ raw h0) v1
 have v3 : Nonempty (Derivation body Delta (graph3 (rightOf (.projection 0)) raw input first second)) :=
   unaryValue InternalUnpair.right (.projection 0) raw input xs (pairRight input typ raw h0) v1
 have v4 : Nonempty (Derivation body Delta (graph3 (rightOf (rightOf (.projection 0))) index input first second)) :=
   unaryValue InternalUnpair.right (rightOf (.projection 0)) index raw xs (pairRight raw (numeral 0) index h1) v3
 have v5 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (.projection 0)) (rightOf (rightOf (.projection 0)))) data input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (.projection 0)) (rightOf (rightOf (.projection 0))) data typ index xs h2 v2 v4
 have v6 : Nonempty (Derivation body Delta (graph3 (pairOf (OriginalRawSyntaxTransport.constant 3 0) (pairOf (leftOf (.projection 0)) (rightOf (rightOf (.projection 0))))) out input first second)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 0) (pairOf (leftOf (.projection 0)) (rightOf (rightOf (.projection 0)))) out (numeral 0) data xs h3 v0 v5
 have v7 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (.projection 0))) (numeral 0) input first second)) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 0) raw xs (pairLeft raw (numeral 0) index h1) v3
 exact dispatch0 input first second out v7 v6

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalVariableProof
