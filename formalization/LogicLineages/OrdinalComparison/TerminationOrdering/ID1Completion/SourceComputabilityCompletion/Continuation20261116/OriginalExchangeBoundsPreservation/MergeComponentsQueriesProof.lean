module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeComponentsQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
def ls : Program 2 := leftOf (.projection 0)
def ll : Program 2 := rightOf (.projection 0)
def rs : Program 2 := leftOf (.projection 1)
def rl : Program 2 := rightOf (.projection 1)
def mx : Program 2 := .composition maximum ![ll,rl]
def queries : Fin 5 → Program 2 := ![ls,ll,rs,rl,mx]

theorem recover (left right : OTerm alpha) (ys : Fin 5 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![left,right]))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing left (ys 0) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing right (ys 2) (ys 3))) ∧
    Nonempty (Derivation body Delta (graph2 maximum (ys 4) (ys 1) (ys 3))) := by
  have h0 := unaryRecover InternalUnpair.left (.projection 0) (ys 0) left ![left,right] (hq 0) (projectionValue 0 ![left,right])
  have h1 := unaryRecover InternalUnpair.right (.projection 0) (ys 1) left ![left,right] (hq 1) (projectionValue 0 ![left,right])
  have h2 := unaryRecover InternalUnpair.left (.projection 1) (ys 2) right ![left,right] (hq 2) (projectionValue 1 ![left,right])
  have h3 := unaryRecover InternalUnpair.right (.projection 1) (ys 3) right ![left,right] (hq 3) (projectionValue 1 ![left,right])
  exact ⟨reconstructPair left (ys 0) (ys 1) h0 h1,reconstructPair right (ys 2) (ys 3) h2 h3,
    binaryRecover maximum ll rl (ys 4) (ys 1) (ys 3) ![left,right] (hq 4) (hq 1) (hq 3)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeComponentsQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeComponentsQueriesProof
