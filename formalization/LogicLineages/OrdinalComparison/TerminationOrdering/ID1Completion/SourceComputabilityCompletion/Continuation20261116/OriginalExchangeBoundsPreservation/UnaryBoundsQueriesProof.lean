module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (suc)
def next : Program 1 := pairOf (OriginalRawSyntaxTransport.succOf InternalUnpair.left) InternalUnpair.right
def queries : Fin 3 → Program 1 := ![InternalUnpair.left,InternalUnpair.right,next]

theorem recover (value : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![value]))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value (ys 0) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 2) (suc (ys 0)) (ys 1))) := by
  have hs := unaryValue .succ InternalUnpair.left (suc (ys 0)) (ys 0) ![value]
    (successorValue ![ys 0]) (hq 0)
  exact ⟨reconstructPair value (ys 0) (ys 1) (hq 0) (hq 1),
    binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.succOf InternalUnpair.left)
      InternalUnpair.right (ys 2) (suc (ys 0)) (ys 1) ![value] (hq 2) hs (hq 1)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsQueriesProof
