module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeArithmeticProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundAlternativeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundStabilityChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRoundAlternativeTargets (budgetStep)
open NumberedWindowInternalSparseRoundAlternativeChecks (exact_RoundAlternative)
open NumberedWindowInternalSparseRoundStabilityChecks (exact_StableNext)
open NumberedWindowInternalSparseRoundChargeTargets

theorem exact_RoundCharge : ExactRoundCharge := by
  intro pred strict E body α Γ vertices ctx ty seed i a b c initial countA countB
  let step := budgetStep E vertices ctx ty seed i a b countA countB
  let runs := step ⊓ roundGraph E c (suc (suc i)) vertices ctx ty seed
  let A := runs ⊓ PrimaryFiniteDescent.budget i initial countA a b
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have stage := Derivation.conjunctionLeft h
  have s := Derivation.conjunctionLeft stage
  have ab := Derivation.conjunctionLeft s
  let inc := PrimaryMonotonicity.included b a
  have next : Nonempty (Derivation body Δ (PrimaryFiniteDescent.budget (suc i) initial countB b c)) := by
    apply formulaCases inc
    · obtain ⟨law⟩ := exact_StableNext pred E body α (inc :: Δ) vertices ctx ty seed i a b c
      have three := Derivation.conjunctionIntroduction (Derivation.conjunctionLeft ab)
        (Derivation.conjunctionIntroduction (Derivation.conjunctionRight ab) (Derivation.conjunctionRight stage))
      have stable := Derivation.implicationElimination law
        (Derivation.conjunctionIntroduction (addHyp three inc) (Derivation.hypothesis List.mem_cons_self))
      exact ⟨orLeft stable⟩
    · have unstable : Derivation body (inc.not :: Δ) inc.not := Derivation.hypothesis List.mem_cons_self
      obtain ⟨law⟩ := exact_RoundAlternative strict E body α (inc.not :: Δ) vertices ctx ty seed i a b countA countB
      have fall := Derivation.implicationElimination (Derivation.implicationElimination law (addHyp s inc.not)) unstable
      have old := Derivation.implicationElimination (addHyp (Derivation.conjunctionRight h) inc.not) unstable
      obtain ⟨charged⟩ := NumberedWindowInternalSparseRoundChargeArithmeticProof.budgetStep i countA countB initial
        ⟨fall⟩ ⟨old⟩
      exact ⟨orRight charged⟩
  obtain ⟨n⟩ := next
  exact ⟨Derivation.implicationIntroduction n⟩

#print axioms exact_RoundCharge
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeChecks
