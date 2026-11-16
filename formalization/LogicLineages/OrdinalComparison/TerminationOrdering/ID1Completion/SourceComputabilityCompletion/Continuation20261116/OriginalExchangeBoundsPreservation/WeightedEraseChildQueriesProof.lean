module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseChildQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseChildQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EraseChildQueriesProof (head tail child)
def tailFold (weight : Program 1) : Program 2 := .composition (Fold.weighted weight) (fun _ : Fin 1 => tail)
def restFold (weight : Program 1) : Program 2 := .composition (Fold.weighted weight) (fun _ : Fin 1 => rightOf child)
def headWeight (weight : Program 1) : Program 2 := .composition weight (fun _ : Fin 1 => head)
def queries (weight : Program 1) : Fin 8 → Program 2 :=
  ![head,tail,child,leftOf child,rightOf child,tailFold weight,restFold weight,headWeight weight]

theorem recover (weight : Program 1) (raw needle : OTerm alpha) (ys : Fin 8 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries weight i) (ys i) ![raw,needle]))) :
    Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) (ys 5) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) (ys 6) (ys 4))) ∧
    Nonempty (Derivation body Delta (graph1 weight (ys 7) (ys 0))) := by
  exact ⟨unaryRecover (Fold.weighted weight) tail (ys 5) (ys 1) ![raw,needle] (hq 5) (hq 1),
    unaryRecover (Fold.weighted weight) (rightOf child) (ys 6) (ys 4) ![raw,needle] (hq 6) (hq 4),
    unaryRecover weight head (ys 7) (ys 0) ![raw,needle] (hq 7) (hq 0)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseChildQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseChildQueriesProof
