module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreement
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement
/-- Equality of actual weighted folds is proved from the original universal
count agreement, not a semantic permutation hypothesis. -/
def fields {alpha : Type} (weight : Program 1) (left right ls rs : OTerm alpha) : Formula alpha :=
  agreement left right ⊓ (graph1 (Fold.weighted weight) ls left ⊓ graph1 (Fold.weighted weight) rs right)
def matrix {alpha : Type} (weight : Program 1) (left : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  (fields weight (left.relabel Sum.inl) (x 0) (x 1) (x 2)).imp (eqn (x 1) (x 2))
def AtRaw {alpha : Type} (weight : Program 1) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix weight raw)
def predicate {alpha : Type} (weight : Program 1) : Formula (alpha ⊕ Fin 1) := AtRaw weight (.var (.inr 0))
def BelowRaw {alpha : Type} (weight : Program 1) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate weight) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreement
