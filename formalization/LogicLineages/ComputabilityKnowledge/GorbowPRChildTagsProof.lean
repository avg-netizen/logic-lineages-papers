module

public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRChildTags.Proof
open GorbowPRProgram GorbowPRRegistry

private theorem nodesNonempty {n : Nat} (p : Program n) : nodes p ≠ [] := by
  cases p <;> simp [nodes]

private theorem flattenStart {α : Type} (xs : List (List α)) (i : Nat)
    (hi : i < xs.length) (hne : xs[i] ≠ []) :
    xs.flatten[(xs.take i).flatten.length]? = xs[i][0]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          cases x with
          | nil => exact False.elim (hne rfl)
          | cons a as => rfl
      | succ i =>
          simp only [List.take_succ_cons, List.flatten_cons, List.length_append,
            List.getElem_cons_succ]
          rw [List.getElem?_append_right (Nat.le_add_right _ _)]
          simp only [Nat.add_sub_cancel_left]
          exact ih i (by simpa using hi) hne

theorem compositionFunction : Targets.CompositionFunction := by
  intro m n f g
  cases f <;> rfl

theorem compositionArgument : Targets.CompositionArgument := by
  intro m n f g i
  let blocks := List.ofFn fun j => nodes (g j)
  have hoff : argumentTag f g i = ((nodes f).length + (blocks.take i.val).flatten.length) + 1 := by
    simp [argumentTag, blocks, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hoff]
  change (nodes f ++ blocks.flatten)[(nodes f).length + (blocks.take i.val).flatten.length]? = _
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]
  have hi : i.val < blocks.length := by simpa [blocks] using i.isLt
  have hn : blocks[i.val] ≠ [] := by simpa [blocks] using nodesNonempty (g i)
  rw [flattenStart blocks i.val hi hn]
  simpa [blocks] using GorbowPRRegistry.Proof.rootTag m (g i)

theorem recursionBase : Targets.RecursionBase := by
  intro n f g
  cases f <;> rfl

theorem recursionStep : Targets.RecursionStep := by
  intro n f g
  have hoff : stepTag f = (nodes f).length + 1 := Nat.add_comm _ _
  rw [hoff]
  change (nodes f ++ nodes g)[(nodes f).length]? = _
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simpa using GorbowPRRegistry.Proof.rootTag (n+2) g

end LogicLineages.ComputabilityKnowledge.GorbowPRChildTags.Proof
