module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariant
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalUniverseDecoderTransport
open Continuation20261114 Continuation20261115
/-- Original Code guard and successful full annotated-entry extraction. -/
def domain {alpha : Type} (n : Nat) (raw entries : OTerm alpha) : Formula alpha :=
  graph1 (OriginalCodeValidityGuard.check n) (suc z) raw ⊓
    graph2 ArgumentEntriesRecursor.extract (suc entries) raw z
/-- Plain typed spine fixes ORDERED annotations, without universe guards. -/
def Plain {alpha : Type} (H : Program 1) (types raw gamma : OTerm alpha) : Formula alpha :=
  OriginalTypedDecoderTransport.Accepted H true types raw gamma
def row {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries gamma context : OTerm alpha) : Formula alpha :=
  (domain n raw entries).imp
    (((Accepted H M W true types raw gamma context).imp (EntryFacts.allGood H M W entries gamma context)) ⊓
      (((Plain H types raw gamma) ⊓ EntryFacts.allGood H M W entries gamma context).imp
        (Accepted H M W true types raw gamma context)))
def matrix {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  let x : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
  row n H M W (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3)
def AtRaw {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n H M W raw)
def predicate {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) : Formula (alpha ⊕ Fin 1) :=
  AtRaw n H M W (.var (.inr 0))
def BelowRaw {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate n H M W) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariant
