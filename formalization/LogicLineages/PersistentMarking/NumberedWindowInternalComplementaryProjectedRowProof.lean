module
public import LogicLineages.PersistentMarking.NumberedWindowInternalComplementaryProjectedRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalComplementaryProjectedRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open NumberedWindowInternalOriginRowsFilterTargets (Report)
open NumberedWindowInternalOriginRowsFilterStepProof (exact_OpenOriginRowStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalComplementaryProjectedRowTargets

theorem exact_OpenComplementaryProjectedRow : ExactOpenComplementaryProjectedRow := by
  intro B α Γ row pool key tailL tailR outL outR tag l r
  let q := memberGraph pool key
  let goal := outcomes row tailL tailR outL outR
  have yes : Report B Γ (q.imp goal) := by
    have q' : Report B (q :: Γ) q := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have lc := (exact_OpenOriginRowStep B α (q :: Γ) row tailL pool key outL (withHyp tag q)).1 q'
    have rc := (exact_OpenOriginRowStep B α (q :: Γ) row tailR pool key outR (withHyp tag q)).1 q'
    obtain ⟨prepended⟩ := lc.1.mp (withHyp l q)
    obtain ⟨unchanged⟩ := rc.2.mp (withHyp r q)
    exact ⟨Derivation.implicationIntroduction (orLeft
      (Derivation.conjunctionIntroduction prepended unchanged))⟩
  have no : Report B Γ (q.not.imp goal) := by
    have q' : Report B (q.not :: Γ) q.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have lc := (exact_OpenOriginRowStep B α (q.not :: Γ) row tailL pool key outL (withHyp tag q.not)).2 q'
    have rc := (exact_OpenOriginRowStep B α (q.not :: Γ) row tailR pool key outR (withHyp tag q.not)).2 q'
    obtain ⟨unchanged⟩ := lc.1.mp (withHyp l q.not)
    obtain ⟨prepended⟩ := rc.2.mp (withHyp r q.not)
    exact ⟨Derivation.implicationIntroduction (orRight
      (Derivation.conjunctionIntroduction unchanged prepended))⟩
  obtain ⟨yes⟩ := yes
  obtain ⟨no⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle q) yes no⟩

#print axioms exact_OpenComplementaryProjectedRow

end LogicLineages.PersistentMarking.NumberedWindowInternalComplementaryProjectedRowProof
