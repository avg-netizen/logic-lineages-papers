module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalBetaTotalityProof (addHyp)
open EvaluatorKeyMinimumSupportProof
attribute [local irreducible] programGraph

theorem actualMinimumEquality : EvaluatorKeyMinimumTargets.ActualMinimumEquality := by
  intro p H G W P body alpha Delta left right out otherOut parameter hl hr hs ho hp
  have hm := minimumFacts p H G W P left out parameter otherOut hl ho
  have hn := minimumFacts p H G W P right otherOut parameter out hr hp
  have rowOut := EvaluatorKeyPutInternalProof.actualRows p H G W P body alpha Delta
    left right out parameter hl hr hs
  have rowOther := EvaluatorKeyPutInternalProof.actualRows p H G W P body alpha Delta
    left right otherOut parameter hl hr hs
  obtain ⟨forward⟩ := andLeft rowOut
  obtain ⟨backward⟩ := andRight rowOther
  obtain ⟨hitOut⟩ := andLeft (andRight hm)
  obtain ⟨hitOther⟩ := andLeft (andRight hn)
  have hitOutRight := Derivation.implicationElimination forward hitOut
  have hitOtherLeft := Derivation.implicationElimination backward hitOther
  obtain ⟨missLeft⟩ := andRight (andRight hm)
  obtain ⟨missRight⟩ := andRight (andRight hn)
  have hforward : Nonempty (Derivation body Delta
      (InternalLessThan.strictLess out otherOut).not) := by
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination
        (Derivation.implicationElimination (addHyp missRight _)
          (Derivation.hypothesis List.mem_cons_self)) (addHyp hitOutRight _))⟩
  have hbackward : Nonempty (Derivation body Delta
      (InternalLessThan.strictLess otherOut out).not) := by
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination
        (Derivation.implicationElimination (addHyp missLeft _)
          (Derivation.hypothesis List.mem_cons_self)) (addHyp hitOtherLeft _))⟩
  exact OriginalActiveKernelMinimumSupportProof.equalOfNotLess out otherOut hforward hbackward
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumProof
