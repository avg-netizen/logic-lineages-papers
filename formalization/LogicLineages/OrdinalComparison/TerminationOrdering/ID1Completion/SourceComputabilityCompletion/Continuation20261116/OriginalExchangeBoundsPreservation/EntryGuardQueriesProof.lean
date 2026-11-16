module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z)
def tailList : Program 2 := consOf (.projection 1) (OriginalRawSyntaxTransport.constant 2 0)
def children : Program 2 := consOf (.projection 0) tailList
def queries : Fin 2 → Program 2 := ![tailList,children]

theorem recover (head tail : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![head,tail]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode (ys 0) tail z)) ∧
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode (ys 1) head (ys 0))) := by
  exact ⟨binaryRecover InternalListCodec.consCode (.projection 1) (OriginalRawSyntaxTransport.constant 2 0)
    (ys 0) tail z ![head,tail] (hq 0) (projectionValue 1 ![head,tail])
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 ![head,tail]),
    binaryRecover InternalListCodec.consCode (.projection 0) tailList (ys 1) head (ys 0) ![head,tail]
      (hq 1) (projectionValue 0 ![head,tail]) (hq 0)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardQueriesProof
