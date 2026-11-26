module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalTwoDeletionParameterDefinitions
/-- Identical twice-erased input and runtime parameter; includes the matching
lookup types in the intermediate contexts. No source or calibration premise. -/
def ActualInputSquare : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight : OTerm alpha),
  Nonempty (Derivation body Delta
    ((fields gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight).imp
      (equal rawLeft rawRight ⊓ (equal paramLeft paramRight ⊓
        (graph2 InternalRawListRecursion.lookup a i upper ⊓
          graph2 InternalRawListRecursion.lookup b j lower)))))

/-- Only functionality at identical inputs of ONE arbitrary Program, not
covariance of a key, minimum, canonical fold, or canonical Object. -/
def ActualObservationSquare : Prop :=
  ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight valueLeft valueRight : OTerm alpha),
  Nonempty (Derivation body Delta
    (((fields gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight) ⊓
      (graph2 R valueLeft rawLeft paramLeft ⊓ graph2 R valueRight rawRight paramRight)).imp
        (equal valueLeft valueRight)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterTargets
