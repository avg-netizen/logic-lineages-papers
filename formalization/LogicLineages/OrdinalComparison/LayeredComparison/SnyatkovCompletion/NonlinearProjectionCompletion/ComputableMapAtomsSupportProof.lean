module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsDefinitions
public import Mathlib.Tactic.SplitIfs
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
open ComputableMapAtoms

theorem children_decreasing {α : Type} : ∀ p q : Call α,
    q ∈ children p → q.2 < p.2 := by
  intro p q h
  by_cases hleaf : p.2 % 6 = 0 ∨ p.2 % 6 = 1 ∨ p.2 % 6 = 2
  · simp [children, hleaf] at h
  have hpos : 0 < p.2 := by omega
  have hd : p.2 / 6 < p.2 := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (p.2 / 6)
  have hr := Nat.unpair_right_le (p.2 / 6)
  rcases q with ⟨args, code⟩
  unfold children at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq]
  all_goals omega
#print axioms children_decreasing

theorem equation {α : Type} (op : α → Nat → Nat) (p : Call α) :
    value op p = assemble op p ((children p).map (value op)) := by
  rcases p with ⟨args, code⟩
  change LinearRows.Code.mapAtoms (op args) code = _
  rw [LinearRows.Code.mapAtoms]
  split_ifs <;> simp_all [children, assemble, value]
#print axioms equation

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
