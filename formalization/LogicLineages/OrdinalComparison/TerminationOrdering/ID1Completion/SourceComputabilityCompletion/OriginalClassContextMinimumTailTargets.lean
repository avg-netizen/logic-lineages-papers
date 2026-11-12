module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open UniformCertificateCompletion OriginalClassContextMinimumTail
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- TOP erasure only: the actual observed minimum output preserves the
original key and rank at the literal tail-context parameter. No class-hit
premise, supplied erased-key agreement, full-fold or arbitrary-cutoff claim. -/
def ActualObservedMinimumTailKeyRank : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed out parameter context extended d gamma tailParameter
      seedObject outObject erasedSeedObject erasedOutObject erasedSeed erasedOut key rank : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premises p H G W P seed out parameter context extended d gamma tailParameter
      seedObject outObject erasedSeedObject erasedOutObject erasedSeed erasedOut).imp
      (Result p.base.oldRepresentative erasedSeed erasedOut tailParameter key rank)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailTargets
