module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsTestProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsGraph
open BoundedSourcePrograms ScopedPhiProgramsGraph BoundedSourceProgramsProof
attribute [local irreducible] Nat.sqrt Nat.unpair Code.guard

abbrev Input := ScopedPhiProgramsGraph.Input

def boundedChildren (p : Input) : List Input :=
  if (Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2).isSome then
    (List.range (ScopedPhiPrograms.Code.value p.1 ((Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2).getD 0))).map
      (fun n => (Code.update p.1 (p.2 / 5).unpair.1 n, (p.2 / 5).unpair.2))
  else []

def children (p : Input) : List Input :=
  if p.2 % 5 = 0 ∨ p.2 % 5 = 1 then []
  else if p.2 % 5 = 2 then [(p.1, p.2 / 5)]
  else if p.2 % 5 = 3 then [(p.1, (p.2 / 5).unpair.1), (p.1, (p.2 / 5).unpair.2)]
  else boundedChildren p

theorem boundedChildren_code (p q : Input) (h : q ∈ boundedChildren p) : q.2 = (p.2 / 5).unpair.2 := by
  unfold boundedChildren at h
  split_ifs at h
  · rcases List.mem_map.mp h with ⟨n, _, rfl⟩
    rfl
  · simp at h

theorem children_decreasing : ∀ p q, q ∈ children p → q.2 < p.2 := by
  intro p q h
  by_cases hleaf : p.2 % 5 = 0 ∨ p.2 % 5 = 1
  · simp [children, hleaf] at h
  have hp : 0 < p.2 := by omega
  have hd := Nat.div_lt_self hp (by decide : 1 < 5)
  have hl := Nat.unpair_left_le (p.2 / 5)
  have hr := Nat.unpair_right_le (p.2 / 5)
  by_cases h2 : p.2 % 5 = 2
  · simp only [children, if_neg hleaf, if_pos h2, List.mem_cons, List.not_mem_nil, or_false] at h
    subst q; exact hd
  by_cases h3 : p.2 % 5 = 3
  · simp only [children, if_neg hleaf, if_neg h2, if_pos h3, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> dsimp <;> omega
  · simp only [children, if_neg hleaf, if_neg h2, if_neg h3] at h
    rw [boundedChildren_code p q h]
    omega

theorem guard_computation : Computable (fun p : Input => Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2) :=
  guard_computable.comp (left_primitive 5).to_comp (right_primitive 5).to_comp

theorem boundedChildren_computable : Computable boundedChildren := by
  have ht : Computable (fun p : Input => (Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2).getD 0) :=
    Computable.option_getD guard_computation (Computable.const 0)
  have hb : Computable (fun p : Input => ScopedPhiPrograms.Code.value p.1
      ((Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2).getD 0)) :=
    ScopedPhiProgramsProof.value_computable.comp Computable.fst ht
  have hs : Computable₂ (fun p : Input => fun n : Nat =>
      (Code.update p.1 (p.2 / 5).unpair.1 n, (p.2 / 5).unpair.2)) :=
    (update_primitive.to_comp.comp ((Computable.fst.comp Computable.fst).pair
      (((left_primitive 5).to_comp.comp Computable.fst).pair Computable.snd))).pair
      ((right_primitive 5).to_comp.comp Computable.fst)
  have hm := computable_map (Primrec.list_range.to_comp.comp hb) hs
  apply (Computable.cond (Primrec.option_isSome.to_comp.comp guard_computation) hm (Computable.const [])).of_eq
  intro p
  unfold boundedChildren
  cases (Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2).isSome <;> rfl

theorem children_computable : Computable children :=
  computable_ite ((tag_is 5 0).or (tag_is 5 1)).decide.to_comp (Computable.const [])
    (computable_ite (tag_is 5 2).decide.to_comp
      (Computable.list_cons.comp (Computable.fst.pair (quotient_primitive 5).to_comp) (Computable.const []))
      (computable_ite (tag_is 5 3).decide.to_comp
        (Computable.list_cons.comp (Computable.fst.pair (left_primitive 5).to_comp)
          (Computable.list_cons.comp (Computable.fst.pair (right_primitive 5).to_comp) (Computable.const [])))
        boundedChildren_computable))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsGraph
