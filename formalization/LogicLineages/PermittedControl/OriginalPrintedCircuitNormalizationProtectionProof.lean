module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationTargets
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationFreshProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNormalization
open OriginalPrintedCircuitSequential (Gate)
open ArbitraryHeadWireList (hiddenNames)

theorem maxSeed (xs : List Nat) (m : Nat) : m ≤ xs.foldr max m := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => exact ih.trans (le_max_right _ _)

theorem maxAt (xs : List Nat) (m n : Nat) (mem : n ∈ xs) : n ≤ xs.foldr max m := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
      rcases List.mem_cons.mp mem with eq | tail
      · subst n
        exact le_max_left _ _
      · exact (ih tail).trans (le_max_right _ _)

theorem exactPrintedProtection : ExactPrintedProtection := by
  intro ext gates
  refine ⟨maxSeed (names gates) ext,?_,?_⟩
  · intro g hg
    refine ⟨maxAt (names gates) ext g.output (List.mem_append_left _ (List.mem_map.mpr ⟨g,hg,rfl⟩)),?_⟩
    intro n hn
    exact maxAt (names gates) ext n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨g,hg,hn⟩))
  · intro n hn
    have fresh := OriginalMixedGateNormalization.exactMixedFreshAliases (protectedCeiling ext gates) (baseGates gates)
    exact lt_of_le_of_lt fresh.1 (fresh.2.2.2 n hn)

end LogicLineages.PermittedControl.OriginalPrintedCircuitNormalization
