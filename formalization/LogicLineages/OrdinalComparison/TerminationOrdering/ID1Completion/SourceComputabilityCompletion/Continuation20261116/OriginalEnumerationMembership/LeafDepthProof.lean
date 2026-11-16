module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.OrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafDepthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 DepthSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem leaf (n : Nat) (raw fuel : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency z raw z))) :
    Nonempty (Derivation body Delta (Targets.depthBound n raw (suc fuel))) :=
  DepthBoundProof.introduce n raw (suc fuel) (suc z)
    (OriginalEnumerationDepth.ValueProof.leaf n raw hv hd)
    (OrderProof.successorForward z (suc fuel) ⟨InternalQuotientComparisonProof.zeroLessSuccessor fuel⟩)

theorem variableCode (n : Nat) (raw index fuel : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index))) :
    Nonempty (Derivation body Delta (Targets.depthBound n raw (suc fuel))) :=
  leaf n raw fuel hv (OriginalEnumerationDepth.ChildrenProof.variableLeaf raw z index hc)

theorem bottom (n : Nat) (raw typ fuel : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw typ))) :
    Nonempty (Derivation body Delta (Targets.depthBound n raw (suc fuel))) :=
  leaf n raw fuel hv (OriginalEnumerationDepth.ChildrenProof.bottom raw z typ hc)

theorem nil (n : Nat) (raw fuel : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (Targets.depthBound n raw (suc fuel))) :=
  leaf n raw fuel hv (OriginalEnumerationDepth.ChildrenProof.nil raw z hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafDepthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafDepthProof
