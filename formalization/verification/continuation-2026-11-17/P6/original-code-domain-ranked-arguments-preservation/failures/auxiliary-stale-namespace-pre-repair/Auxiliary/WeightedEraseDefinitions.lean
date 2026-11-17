module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseInvariantDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedErase
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.BoundsRecombination (merge)
/-- The actual fold is unchanged if deletion finds no occurrence, and is the
merge of the removed weight and the remaining fold if it finds one. -/
def effect {alpha : Type} (bit total remainingWeight needleWeight : OTerm alpha) : Formula alpha :=
  ((eqn bit z).imp (eqn total remainingWeight)) ⊓
  ((eqn bit (suc z)).imp (graph2 merge total needleWeight remainingWeight))
def fields {alpha : Type} (weight : Program 1)
    (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha) : Formula alpha :=
  EraseInvariant.fields raw needle acc bit rest ⊓
  (graph1 (Fold.weighted weight) total raw ⊓
   (graph1 (Fold.weighted weight) remainingWeight rest ⊓ graph1 weight needleWeight needle))
def matrix {alpha : Type} (weight : Program 1) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  let x : Fin 7 → OTerm (alpha ⊕ Fin 7) := fun i => .var (.inr i)
  (fields weight (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)).imp
    (effect (x 2) (x 4) (x 5) (x 6))
def AtRaw {alpha : Type} (weight : Program 1) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix weight raw)
def predicate {alpha : Type} (weight : Program 1) : Formula (alpha ⊕ Fin 1) := AtRaw weight (.var (.inr 0))
def BelowRaw {alpha : Type} (weight : Program 1) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate weight) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedErase
