module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sameRaw (n : Nat) (left right leftBounds rightBounds : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn left right)))
    (hl : Nonempty (Derivation body Delta
      (graph1 (Continuation20261115.OriginalCodeBoundsRecursion.bounds n) leftBounds left)))
    (hr : Nonempty (Derivation body Delta
      (graph1 (Continuation20261115.OriginalCodeBoundsRecursion.bounds n) rightBounds right))) :
    Nonempty (Derivation body Delta (eqn leftBounds rightBounds)) := by
  have ht := headTransport (Continuation20261115.OriginalCodeBoundsRecursion.bounds n)
    leftBounds left right (fun i : Fin 0 => Fin.elim0 i) he hl
  exact valueUnique (Continuation20261115.OriginalCodeBoundsRecursion.bounds n)
    leftBounds rightBounds ![right] ht hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TransportProof
