module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalBottomProof
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

theorem bottomLaw : OriginalHereditaryReturnInternalTargets.BottomLaw := by
 intro body alpha Delta input first second typ raw out h0 h1 h2
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have v0 : Nonempty (Derivation body Delta (graph3 (OriginalRawSyntaxTransport.constant 3 3) (numeral 3) input first second)) :=
   constantValue 3 xs
 have v1 : Nonempty (Derivation body Delta (graph3 (.projection 0) input input first second)) :=
   projectionValue 0 xs
 have v2 : Nonempty (Derivation body Delta (graph3 (leftOf (.projection 0)) typ input first second)) :=
   unaryValue InternalUnpair.left (.projection 0) typ input xs (pairLeft input typ raw h0) v1
 have v3 : Nonempty (Derivation body Delta (graph3 (pairOf (OriginalRawSyntaxTransport.constant 3 3) (leftOf (.projection 0))) out input first second)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 3) (leftOf (.projection 0)) out (numeral 3) typ xs h2 v0 v2
 have v4 : Nonempty (Derivation body Delta (graph3 (rightOf (.projection 0)) raw input first second)) :=
   unaryValue InternalUnpair.right (.projection 0) raw input xs (pairRight input typ raw h0) v1
 have v5 : Nonempty (Derivation body Delta (graph3 (leftOf (rightOf (.projection 0))) (numeral 3) input first second)) :=
   unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 3) raw xs (pairLeft raw (numeral 3) typ h1) v4
 exact dispatch3 input first second out v5 v3

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalBottomProof
