module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.AcceptanceConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariant
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalUniverseDecoderTransport
open Continuation20261114 Continuation20261115
/-- Original domain/extraction/type-list observations, with no typing conclusion assumed. -/
def domain {alpha : Type} (n : Nat) (raw count types entries : OTerm alpha) : Formula alpha :=
  graph1 (OriginalCodeValidityGuard.check n) (suc z) raw ⊓
    (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z ⊓
      graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)
/-- Source-to-extraction invariant: exact length and pointwise original guarded entry checks. -/
def invariant {alpha : Type} (H : Program 1) (M W : Program 2)
    (count entries gamma context : OTerm alpha) : Formula alpha :=
  graph1 OriginalContextInsertion.length count entries ⊓ EntryFacts.allGood H M W entries gamma context
/-- Both directions are proved by original raw-code induction. Successful target typing
is a conclusion, not part of the shared domain premise. -/
def row {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2)
    (raw count types entries gamma context : OTerm alpha) : Formula alpha :=
  (domain n raw count types entries).imp
    (((Accepted H M W true types raw gamma context).imp (invariant H M W count entries gamma context)) ⊓
      ((invariant H M W count entries gamma context).imp (Accepted H M W true types raw gamma context)))
def matrix {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  let x : Fin 5 → OTerm (alpha ⊕ Fin 5) := fun i => .var (.inr i)
  row n H M W (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4)
def AtRaw {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n H M W raw)
def predicate {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) : Formula (alpha ⊕ Fin 1) :=
  AtRaw n H M W (.var (.inr 0))
def BelowRaw {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate n H M W) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariant
