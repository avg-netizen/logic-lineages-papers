module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.RankFoldQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
def leftFold (n : Nat) : Program 2 := .composition (Continuation20261116.OriginalExchangeBoundsPreservation.Fold.weighted rankWeight) (fun _ : Fin 1 => .projection 0)
def rightFold (n : Nat) : Program 2 := .composition (Continuation20261116.OriginalExchangeBoundsPreservation.Fold.weighted rankWeight) (fun _ : Fin 1 => .projection 1)
def queries (n : Nat) : Fin 2 → Program 2 := ![leftFold n,rightFold n]

theorem recover (n : Nat) (left right : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries n i) (ys i) ![left,right]))) :
    Nonempty (Derivation body Delta (graph1 (Continuation20261116.OriginalExchangeBoundsPreservation.Fold.weighted rankWeight) (ys 0) left)) ∧
    Nonempty (Derivation body Delta (graph1 (Continuation20261116.OriginalExchangeBoundsPreservation.Fold.weighted rankWeight) (ys 1) right)) := by
  exact ⟨unaryRecover (Continuation20261116.OriginalExchangeBoundsPreservation.Fold.weighted rankWeight) (.projection 0) (ys 0) left ![left,right]
    (hq 0) (projectionValue 0 ![left,right]),
    unaryRecover (Continuation20261116.OriginalExchangeBoundsPreservation.Fold.weighted rankWeight) (.projection 1) (ys 1) right ![left,right]
      (hq 1) (projectionValue 1 ![left,right])⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.RankFoldQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.RankFoldQueriesProof
