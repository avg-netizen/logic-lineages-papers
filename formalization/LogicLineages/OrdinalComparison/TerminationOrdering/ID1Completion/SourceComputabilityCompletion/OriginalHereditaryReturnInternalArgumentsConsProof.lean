module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalArgumentsConsProof
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

theorem argumentsConsLaw : OriginalHereditaryReturnInternalTargets.ArgumentsConsLaw := by
 intro body alpha Delta input first second payload typ children headRaw tailRaw observed out h0 h1 h2 h3 h4
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have v0 : Nonempty (Derivation body Delta (graph3 (.projection 0) input input first second)) :=
   projectionValue 0 xs
 have v1 : Nonempty (Derivation body Delta (graph3 (rightOf (.projection 0)) payload input first second)) :=
   unaryValue InternalUnpair.right (.projection 0) payload input xs (pairRight input (numeral 7) payload h0) v0
 have v2 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (.projection 0))) typ input first second)) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) typ payload xs (pairLeft payload typ children h1) v1
 have v3 : Nonempty (Derivation body Delta (graph3 (.projection 1) first input first second)) :=
   projectionValue 1 xs
 have v4 : Nonempty (Derivation body Delta (graph3 (pairOf (leftOf (rightOf (.projection 0))) (.projection 1)) observed input first second)) :=
   binaryValue InternalPairing.pairing (leftOf (rightOf (.projection 0))) (.projection 1) observed typ first xs h3 v2 v3
 have v5 : Nonempty (Derivation body Delta (graph3 (.projection 2) second input first second)) :=
   projectionValue 2 xs
 have v6 : Nonempty (Derivation body Delta (graph3 (consOf (pairOf (leftOf (rightOf (.projection 0))) (.projection 1)) (.projection 2)) out input first second)) :=
   binaryValue InternalListCodec.consCode (pairOf (leftOf (rightOf (.projection 0))) (.projection 1)) (.projection 2) out observed second xs h4 v4 v5
 exact v6

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalArgumentsConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalArgumentsConsProof
