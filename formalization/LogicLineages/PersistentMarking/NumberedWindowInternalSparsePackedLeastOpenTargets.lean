module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen

/-- Arbitrary programs, settings, context and open terms. Successful
physical packed least yields, in the same calculus and context, an
existential nonzero context tag, the computed member pool on the same
tape, and occurrence of the same selected term in that pool. No
calibration, validity, decoded list or semantic premise. Occurrence only:
not parser inversion, round ancestry, RawMatching or least semantics. -/
def ExactOpenPackedLeastPoolOccurrence : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α),
    Nonempty (Derivation body Γ
      ((leastGraph C X W s ctx ty seed selected).imp
        (poolOccurrence C X W s ctx ty seed selected)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
