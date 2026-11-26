module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PairScalarProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof (pairLeft pairRight)
open InternalControlGraphSupportProof (valueUnique)
open InternalTagArithmeticSyntaxProof (eqn)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sizeUnique (pair size label size' label' : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (h' : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size' label'))) :
    Nonempty (Derivation body Delta (eqn size size')) :=
  valueUnique InternalUnpair.left size size' ![pair]
    (pairLeft pair size label h) (pairLeft pair size' label' h')

theorem labelUnique (pair size label size' label' : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (h' : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size' label'))) :
    Nonempty (Derivation body Delta (eqn label label')) :=
  valueUnique InternalUnpair.right label label' ![pair]
    (pairRight pair size label h) (pairRight pair size' label' h')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PairScalarProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PairScalarProof
