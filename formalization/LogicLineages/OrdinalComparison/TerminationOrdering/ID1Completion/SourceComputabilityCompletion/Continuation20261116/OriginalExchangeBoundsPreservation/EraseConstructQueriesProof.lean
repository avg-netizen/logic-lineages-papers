module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseBranchAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseConstructQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def kept : Program 3 := consOf (.projection 1) (.projection 2)
def paired : Program 3 := pairOf (.projection 0) kept
def queries : Fin 2 → Program 3 := ![kept,paired]

theorem recover (bit head rest : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![bit,head,rest]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode (ys 0) head rest)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 1) bit (ys 0))) := by
  constructor
  · exact binaryRecover InternalListCodec.consCode (.projection 1) (.projection 2) (ys 0) head rest ![bit,head,rest]
      (hq 0) (projectionValue 1 ![bit,head,rest]) (projectionValue 2 ![bit,head,rest])
  · exact binaryRecover InternalPairing.pairing (.projection 0) kept (ys 1) bit (ys 0) ![bit,head,rest]
      (hq 1) (projectionValue 0 ![bit,head,rest]) (hq 0)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseConstructQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseConstructQueriesProof
