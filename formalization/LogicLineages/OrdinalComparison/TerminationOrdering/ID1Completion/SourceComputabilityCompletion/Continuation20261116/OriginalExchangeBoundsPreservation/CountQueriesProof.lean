module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountKeepAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def queries : Fin 2 → Program 3 :=
  ![.composition ArgumentEntryCount.count ![.projection 0,.projection 2],
    .composition ArgumentEntryCount.count ![.projection 1,.projection 2] ]

theorem recover (left right query : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![left,right,query]))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count (ys 0) left query)) ∧
    Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count (ys 1) right query)) := by
  constructor
  · exact binaryRecover ArgumentEntryCount.count (.projection 0) (.projection 2) (ys 0) left query ![left,right,query]
      (hq 0) (projectionValue 0 ![left,right,query]) (projectionValue 2 ![left,right,query])
  · exact binaryRecover ArgumentEntryCount.count (.projection 1) (.projection 2) (ys 1) right query ![left,right,query]
      (hq 1) (projectionValue 1 ![left,right,query]) (projectionValue 2 ![left,right,query])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountQueriesProof
