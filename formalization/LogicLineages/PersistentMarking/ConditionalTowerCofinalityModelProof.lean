module

public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityModelTargets
import LogicLineages.PersistentMarking.ConditionalTowerCofinalityProof

public section

namespace LogicLineages.PersistentMarking.ConditionalTowerCofinality

/-- (P) in the toy model: `ξ + 1` is the least positive `θ` lying strictly
above `η + 1` for every `η < ξ`. -/
theorem toyCharacterization : CharacterizationP toyModel := by
  intro ξ
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ENat) < ξ + 1
    exact lt_of_lt_of_le zero_lt_one le_add_self
  · intro η hη _
    change η < ξ at hη
    show η + 1 < ξ + 1
    lift η to ℕ using ne_top_of_lt hη
    induction ξ using ENat.recTopCoe with
    | top =>
      rw [top_add]
      exact_mod_cast ENat.coe_lt_top (η + 1)
    | coe n =>
      have h1 : η < n := by exact_mod_cast hη
      exact_mod_cast Nat.succ_lt_succ h1
  · intro θ hθ H
    change (0 : ENat) < θ at hθ
    change ∀ η : ENat, η < ξ → (0 : ENat) < θ → η + 1 < θ at H
    show ξ + 1 ≤ θ
    induction θ using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction ξ using ENat.recTopCoe with
      | top =>
        exfalso
        have h1 : ((m : ℕ) : ENat) + 1 < (m : ENat) := H m (ENat.coe_lt_top m) hθ
        have h2 : m + 1 < m := by exact_mod_cast h1
        omega
      | coe n =>
        have hm : 0 < m := by exact_mod_cast hθ
        suffices h : n + 1 ≤ m by exact_mod_cast h
        rcases n with _ | k
        · omega
        · have h1 : ((k : ℕ) : ENat) + 1 < (m : ENat) :=
            H k (by exact_mod_cast Nat.lt_succ_self k) hθ
          have h2 : k + 1 < m := by exact_mod_cast h1
          omega

theorem toyModelSatisfiesHypotheses : ToyModelSatisfiesHypotheses where
  characterization := toyCharacterization
  increasing := by
    intro n
    show ((n : ℕ) : ENat) < ((n + 1 : ℕ) : ENat)
    exact_mod_cast Nat.lt_succ_self n
  below := fun n => ENat.coe_lt_top n
  cofinal := by
    intro η hη
    change η < (⊤ : ENat) at hη
    lift η to ℕ using ne_top_of_lt hη
    refine ⟨η + 1, ?_⟩
    show ((η : ℕ) : ENat) < ((η + 1 : ℕ) : ENat)
    exact_mod_cast Nat.lt_succ_self η
  normBound := fun _ => le_refl (0 : ENat)
  criticalAboveOne := fun _ h => h
  criticalSup := by
    intro f _ hc θ hθ
    have h0 : (0 : ENat) < f 0 := hc 0
    exact lt_of_lt_of_le h0 (hθ.1 ⟨0, rfl⟩)

theorem towerHypothesesConsistent : TowerHypothesesConsistent :=
  ⟨toyModel, toyModelSatisfiesHypotheses⟩

theorem toyModelConclusion : ToyModelConclusion := by
  refine ⟨⟨fun _ _ => le_top, fun b hb => ?_⟩, ?_⟩
  · induction b using ENat.recTopCoe with
    | top => exact le_rfl
    | coe m =>
      exfalso
      have h1 : ((m : ℕ) : ENat) + 1 ≤ (m : ENat) := hb ⟨m, rfl⟩
      have h2 : m + 1 ≤ m := by exact_mod_cast h1
      omega
  · show (⊤ : ENat) + 1 = ⊤
    exact top_add 1

theorem toyModelConditionalInstance : ToyModelConditionalInstance :=
  conditionalTowerSupremum.{0, 0} ENat ENat toyModel toyModelSatisfiesHypotheses

#print axioms toyCharacterization
#print axioms toyModelSatisfiesHypotheses
#print axioms towerHypothesesConsistent
#print axioms toyModelConclusion
#print axioms toyModelConditionalInstance
end LogicLineages.PersistentMarking.ConditionalTowerCofinality
