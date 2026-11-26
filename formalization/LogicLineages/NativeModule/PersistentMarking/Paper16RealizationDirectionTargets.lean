module

public import LogicLineages.NativeModule.PersistentMarking.NativeRealizationCompleteTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16RealizationDirectionTargets
open NativeOrdinalRealizationTargets NativeIteratorStrictTargets NativeIndexedCarrierTargets
open OrdinalRealizationTargets

/-- The direction as printed: a realizing term is replaced by its strict
predecessor. The order is `below predecessor original`. -/
def RealizationToPredecessor (terms : TermStructure) (wf : WellFounded (terms.below .base)) : Prop :=
  ∀ A (s t : terms.term A) (v : Value A),
    terms.below A t s → Realizes terms wf A s v → Realizes terms wf A t v

/-- The printed closure clauses and native typed lambda theorem. -/
def PrintedRealization : Prop :=
  (ExactSemanticShapes ∧ PointwiseSupremumExists ∧
    ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
      RealizationToPredecessor (nativeTerms S) wf ∧
      RealizationDownward (nativeTerms S) wf ∧
      RealizationCountableSupremum (nativeTerms S) wf) ∧
  TypedLambdaRealization.FullTypedLambdaFragment

/-- A diagnostic for the printed strict clause on the same closed native
terms, realized ordinal type, and strict relation. -/
def PrintedDirectionCounterexample : Prop :=
  ∃ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∃ (s t : (nativeTerms S).term .base) (v : Value .base),
      (nativeTerms S).below .base t s ∧
      Realizes (nativeTerms S) wf .base s v ∧
      ¬ Realizes (nativeTerms S) wf .base t v

/-- Candidate for a coordinated wording correction: from the strict
predecessor to the original, including the finite-chain proof statement. -/
def BackwardRealization : Prop := NativeRealizationComplete.FullRealization

end LogicLineages.PersistentMarking.Paper16RealizationDirectionTargets
