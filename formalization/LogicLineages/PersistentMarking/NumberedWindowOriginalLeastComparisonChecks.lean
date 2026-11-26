import LogicLineages.PersistentMarking.NumberedWindowOriginalLeastCutTargets
import LogicLineages.PersistentMarking.NumberedWindowOriginalPresentationChecks

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalLeastComparisonChecks
open NumberedWindowOriginalLeastCutTargets NumberedWindowPresentationLeast
open NumberedWindowOriginalPresentationChecks NumberedWindowExternalIDOperators
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowPresentationCheckers (checks)

theorem exact_LeastAndSentenceComparison : LeastAndSentenceComparison := by
  intro S K hk
  have same (n) : least (checks S.entries (fixed S K)) n ↔ Least (taggedStep S K) n := by
    constructor
    · intro h P hP
      exact h P (fun z hz => hP z (((exact_ActualOperatorAndTerms S K hk P).1 z).mp hz))
    · intro h P hP
      exact h P (fun z hz => hP z (((exact_ActualOperatorAndTerms S K hk P).1 z).mpr hz))
  refine ⟨same,?_⟩
  have eqq : least (checks S.entries (fixed S K)) = Least (taggedStep S K) :=
    funext fun z => propext (same z)
  rw [eqq]
  exact (exact_ActualOperatorAndTerms S K hk _).2

theorem exact_OriginalCut : OriginalCut := by
  intro comp mem S K hk
  obtain ⟨a,b⟩ := comp S K hk
  exact ⟨a,b.mpr (mem S K hk)⟩

#print axioms exact_LeastAndSentenceComparison
#print axioms exact_OriginalCut
end LogicLineages.PersistentMarking.NumberedWindowOriginalLeastComparisonChecks
