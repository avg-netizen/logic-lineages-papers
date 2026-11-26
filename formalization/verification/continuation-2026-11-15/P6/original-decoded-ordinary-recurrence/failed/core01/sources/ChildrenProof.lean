module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.ChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
open NumericDependencyCross
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rawOrdinary (source target sigma tau q r qs rs child deps : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target tau r)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode qs q z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rs r z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z))) :
    Nonempty (Derivation body Delta (graph2 rawDependencies deps source target)) := by
  let xs : Fin 2 → OTerm alpha := ![source,target]
  have hqs := ArgumentEntriesChildren.InternalProof.internalUnary body alpha Delta true source sigma q qs hs hq
  have hrs := ArgumentEntriesChildren.InternalProof.internalUnary body alpha Delta true target tau r rs ht hr
  have hl := unaryValue ArgumentEntriesChildren.children (.projection 0) qs source xs hqs (projectionValue 0 xs)
  have hh := unaryValue ArgumentEntriesChildren.children (.projection 1) rs target xs hrs (projectionValue 1 xs)
  exact binaryValue cross (.composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 0))
    (.composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 1)) deps qs rs xs
    (OriginalDecodedLambdaRecurrence.SingletonProof.crossSingleton q r qs rs child deps hq hr hp hd) hl hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.ChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.ChildrenProof
