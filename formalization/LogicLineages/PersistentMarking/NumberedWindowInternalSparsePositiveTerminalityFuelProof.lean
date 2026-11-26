module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityFuelProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLeastNumberProof (actualNothingBelowZero actualRightSuccessorSplit)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem belowSuccZero (cert : OTerm α) (goal : Formula α)
    (bound : Nonempty (Derivation body Γ (ltF cert (suc z))))
    (nonzero : Nonempty (Derivation body Γ (eqn cert z).not)) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨rule⟩ := actualRightSuccessorSplit body α cert z
  rw [onEquality] at rule
  obtain ⟨split⟩ := closedApply ⟨rule⟩ bound
  obtain ⟨nz⟩ := nonzero
  let lt := ltF cert z
  let eq := eqn cert z
  have left : Nonempty (Derivation body (lt :: Γ) (⊥ : Formula α)) :=
    closedApply (actualNothingBelowZero body α cert) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨l⟩ := left
  have r : Derivation body (eq :: Γ) (⊥ : Formula α) :=
    Derivation.implicationElimination (addHyp nz eq) (Derivation.hypothesis List.mem_cons_self)
  exact ⟨disjunctionElimination split
    (Derivation.implicationIntroduction (Derivation.explosion l))
    (Derivation.implicationIntroduction (Derivation.explosion r))⟩

theorem fuelSuccessorCases (cert fuel : OTerm α) (goal : Formula α)
    (bound : Nonempty (Derivation body Γ (ltF cert (suc fuel))))
    (nonzero : Nonempty (Derivation body Γ (eqn cert z).not))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (pred : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (eqn (fuel.relabel j) (suc pred))) →
      Nonempty (Derivation body Δ (ltF (cert.relabel j) (suc (suc pred)))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply zeroSuccessorCases Γ fuel goal
  · obtain ⟨b⟩ := bound
    obtain ⟨nz⟩ := nonzero
    let e := eqn fuel z
    have hz : Derivation body (e :: Γ) e := Derivation.hypothesis List.mem_cons_self
    exact belowSuccZero cert goal ⟨orderRight cert (congSuc hz) (addHyp b e)⟩ ⟨addHyp nz e⟩
  · intro β j Δ pred hJ eq
    have b := renameInto bound j Δ hJ
    rw [orderRename,sucRelabel] at b
    obtain ⟨d⟩ := b
    obtain ⟨e⟩ := eq
    exact k β j Δ pred hJ ⟨e⟩ ⟨orderRight (cert.relabel j) (congSuc e) d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityFuelProof
