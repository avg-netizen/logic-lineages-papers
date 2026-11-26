module
public import LogicLineages.PermittedControl.ActualEffectiveGlobalTailTargets
import LogicLineages.PermittedControl.ActualEffectiveGlobalTailCalibrationProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailDominanceProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveGlobalTail
open PreparedProjection MixedSameRankResidue ActualZeroEdgeAlphabet
open ActualFiniteGlobalTail ActualSyntaxChargeBudget

theorem exactTailDominance : ExactTailDominance := by
  have dominates (B r : Nat) (terms : List WeightedOperand) :
      globalTail B r terms ≤ inputTailCode B r (terms.map encodeWeighted) := by
    rw [inputLiteral B r terms]
    let original := globalAlphabet r terms
    let bigger := (List.range (syntaxBudget r terms+1)).flatMap
      (fun depth => expandSteps depth (terms.map Prod.snd))
    have subset (op : LowerOperand) (member : op ∈ original) : op ∈ bigger := by
      obtain ⟨depth,inRange,atDepth⟩ := List.mem_flatMap.mp member
      have limited : depth < syntaxCharge r terms + 1 := List.mem_range.mp inRange
      have budgets := (exactChargeBudget.2.1 r terms)
      have bound : syntaxCharge r terms + 1 ≤ syntaxBudget r terms + 1 := Nat.succ_le_succ budgets
      exact List.mem_flatMap.mpr ⟨depth,List.mem_range.mpr (limited.trans_le bound),atDepth⟩
    exact exactAlphabetTailDominance B (unitTerms original) bigger (by
      intro t member
      obtain ⟨op,prior,eq⟩ := List.mem_map.mp member
      subst t
      exact subset op prior)
  refine ⟨dominates,?_⟩
  intro B r ρ terms paid t member
  exact (dominates B r terms).trans (paid t member)

end LogicLineages.PermittedControl.ActualEffectiveGlobalTail
