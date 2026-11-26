module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionArithmeticProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundAlternativeChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.BoundProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalQuotientComparisonProof (orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open ID1Completion.InternalAdditionLawsProof (add leftZero)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open NumberedWindowInternalSparseRoundAlternativeTargets (budgetStep)
open NumberedWindowInternalSparseRoundAlternativeChecks (exact_RoundAlternative)
open NumberedWindowInternalSparseDirectedRounds (poolLength)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRoundExhaustionTargets

theorem exact_InitialBudget : ExactInitialBudget := by
  intro body α Γ vertices size before after count
  let A := unary poolLength size vertices ⊓ graph2 PrimaryUncoveredCount.count count vertices before
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have bound := PrimaryUncoveredCount.BoundProof.internalBound body α Δ vertices before count size
    ⟨Derivation.conjunctionRight h⟩ ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨base⟩ := PrimaryUncoveredCount.OrderProof.transport count size (add z count) size
    ⟨symm (leftZero count)⟩ ⟨refl _⟩ bound
  exact ⟨Derivation.implicationIntroduction (orRight base)⟩

theorem exact_ExhaustedBudget : ExactExhaustedBudget := by
  intro strict E body α Γ vertices ctx ty seed size before after countA countB
  let step := budgetStep E vertices ctx ty seed size before after countA countB
  let A := step ⊓ PrimaryFiniteDescent.budget size size countA before after
  let inc := PrimaryMonotonicity.included after before
  let Δ := inc.not :: A :: Γ
  have given : Derivation body Δ A := Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have no : Derivation body Δ inc.not := Derivation.hypothesis List.mem_cons_self
  obtain ⟨zero⟩ := NumberedWindowInternalSparseRoundExhaustionArithmeticProof.budgetZero size countA
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight given) no⟩
  obtain ⟨alt⟩ := exact_RoundAlternative strict E body α Δ vertices ctx ty seed size before after countA countB
  have fall := Derivation.implicationElimination (Derivation.implicationElimination alt (Derivation.conjunctionLeft given)) no
  obtain ⟨least⟩ := ID1Completion.InternalLeastNumberProof.actualNothingBelowZero body α countB
  exact ⟨Derivation.implicationIntroduction (Derivation.classical (Derivation.implicationElimination
    (weakenClosed least Δ) (orderRight countB zero fall)))⟩

#print axioms exact_InitialBudget
#print axioms exact_ExhaustedBudget
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionChecks
