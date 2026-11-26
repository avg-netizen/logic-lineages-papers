module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeInductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeChildQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Continuation20261115
def node : Program 2 := pairOf (.projection 0) (.projection 1)
def leftBounds (n : Nat) : Program 2 := .composition (OriginalCodeBoundsRecursion.bounds n) (fun _ : Fin 1 => .projection 0)
def rightBounds (n : Nat) : Program 2 := .composition (OriginalCodeBoundsRecursion.bounds n) (fun _ : Fin 1 => .projection 1)
def queries (n : Nat) : Fin 3 → Program 2 := ![node,leftBounds n,rightBounds n]

theorem recover (n : Nat) (left right : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries n i) (ys i) ![left,right]))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) left right)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) (ys 1) left)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) (ys 2) right)) := by
  exact ⟨binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) (ys 0) left right ![left,right]
    (hq 0) (projectionValue 0 ![left,right]) (projectionValue 1 ![left,right]),
    unaryRecover (OriginalCodeBoundsRecursion.bounds n) (.projection 0) (ys 1) left ![left,right]
      (hq 1) (projectionValue 0 ![left,right]),
    unaryRecover (OriginalCodeBoundsRecursion.bounds n) (.projection 1) (ys 2) right ![left,right]
      (hq 2) (projectionValue 1 ![left,right])⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeChildQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeChildQueriesProof
