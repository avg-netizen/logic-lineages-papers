module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryParameterProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralIntro)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof (lambdaTag lambdaDomain)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem parameterValue (input domain child parameter window gamma extended childParameter : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor input domain child)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter window extended))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstParameter childParameter input parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 have hwindow : Nonempty (Derivation body Delta (programGraph (leftOf (.projection 1)) window xs)) :=
   unaryValue InternalUnpair.left (.projection 1) window parameter xs (pairLeft parameter window gamma hp) (projectionValue 1 xs)
 have hgamma : Nonempty (Derivation body Delta (programGraph (rightOf (.projection 1)) gamma xs)) :=
   unaryValue InternalUnpair.right (.projection 1) gamma parameter xs (pairRight parameter window gamma hp) (projectionValue 1 xs)
 have hdomain := lambdaDomain (.projection 0) input domain child xs (projectionValue 0 xs) hctor
 let ext : Program 2 := OriginalHereditaryExpansion.consOf (leftOf (rightOf (.projection 0))) (rightOf (.projection 1))
 have hext : Nonempty (Derivation body Delta (programGraph ext extended xs)) :=
   binaryValue InternalListCodec.consCode (leftOf (rightOf (.projection 0))) (rightOf (.projection 1))
     extended domain gamma xs he hdomain hgamma
 have hpair : Nonempty (Derivation body Delta (programGraph (pairOf (leftOf (.projection 1)) ext) childParameter xs)) :=
   binaryValue InternalPairing.pairing (leftOf (.projection 1)) ext childParameter window extended xs hcp hwindow hext
 apply branchNumeralIntro 1 1 (leftOf (.projection 0)) _ _ childParameter xs
   (lambdaTag (.projection 0) input domain child xs (projectionValue 0 xs) hctor)
 exact hpair
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryParameterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryParameterProof
