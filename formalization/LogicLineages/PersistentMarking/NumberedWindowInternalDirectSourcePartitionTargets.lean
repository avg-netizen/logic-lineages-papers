module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison (permutation)
open ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement (agreement)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowFieldAlgorithm (unpack)

open NumberedWindowInternalDirectSourcePartitionRawTargets

/-- This tape is decoded source, decoded kept, decoded removed. Duplicates
are never removed: the old count program receives the actual ordered
scratch append of slots 1 and 2, not an externally chosen equivalent list. -/
abbrev partitionScratch : Program 3 := observePartition permutation
abbrev partitionCall : Program 3 := decodedCall partitionScratch
abbrev sourcePartition : Program 3 := rawSourceCheck partitionScratch

def expected (src kept removed : Nat) : Bool :=
  match unpack src, unpack kept, unpack removed with
  | some s, some k, some r => decide (s.Perm (k ++ r))
  | _,_,_ => false

def ExactNumericSourcePartition : Prop :=
  ∀ src kept removed : Nat,
    evaluate sourcePartition (src ::ᵥ kept ::ᵥ removed ::ᵥ nil) = (expected src kept removed).toNat

structure PartitionReports (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (src kept removed ds dk dr both : OTerm α) : Prop where
  parsed : ParsedTriplet B Γ src kept removed ds dk dr
  appended : Nonempty (Derivation B Γ (programGraph append both ![dk,dr]))
  countAgreement : Nonempty (Derivation B Γ (agreement ds both))

def ExactOpenSourcePartition : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (src kept removed : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph sourcePartition (suc z) (sourceTape src kept removed))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ds dk dr both : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      PartitionReports B Δ (src.relabel j) (kept.relabel j) (removed.relabel j) ds dk dr both →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionTargets
