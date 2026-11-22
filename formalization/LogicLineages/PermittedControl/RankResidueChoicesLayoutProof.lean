module
public import LogicLineages.PermittedControl.RankResidueChoicesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.RankResidueChoices

theorem namedSlotsExact (ranks : List Nat) :
    (namedSlots ranks).map Prod.snd = ranks ∧
      (namedSlots ranks).map Prod.fst = (List.range ranks.length).map Nat.succ := by
  constructor
  · change ((List.range ranks.length).map (fun i => (i+1,ranks[i]?.getD 0))).map Prod.snd = ranks
    rw [List.map_map]
    apply List.ext_getElem
    · simp
    · intro i valid atRank
      simp only [List.getElem_map,List.getElem_range,Function.comp_apply,
        List.getElem?_eq_getElem atRank,Option.getD_some]
  · simp [namedSlots,List.map_map,Function.comp_def,Nat.succ_eq_add_one]

private theorem assignmentOfMem (m : Nat) (slots : List Slot) (cell : Cell)
    (member : cell ∈ choices m slots) : Assignment (2*m) slots cell := by
  induction slots generalizing cell with
  | nil =>
    have empty : cell = [] := by simpa [choices] using member
    subst cell
    exact .nil
  | cons s ss ih =>
    change cell ∈ (List.range (2*m)).flatMap
      (fun j => (choices m ss).map (fun tail => (s.1,s.2,j) :: tail)) at member
    obtain ⟨j,possible,atDigit⟩ := List.mem_flatMap.mp member
    obtain ⟨tail,inTail,output⟩ := List.mem_map.mp atDigit
    subst cell
    exact .cons (List.mem_range.mp possible) (ih tail inTail)

private theorem memOfAssignment (m : Nat) {slots : List Slot} {cell : Cell}
    (assigned : Assignment (2*m) slots cell) : cell ∈ choices m slots := by
  induction assigned with
  | nil => simp [choices]
  | @cons s j ss tail within rest ih =>
    change (s.1,s.2,j) :: tail ∈ (List.range (2*m)).flatMap
      (fun k => (choices m ss).map (fun ts => (s.1,s.2,k) :: ts))
    exact List.mem_flatMap.mpr ⟨j,List.mem_range.mpr within,List.mem_map.mpr ⟨tail,ih,rfl⟩⟩

theorem choicesExact (m : Nat) (slots : List Slot) (cell : Cell) :
    cell ∈ choices m slots ↔ Assignment (2*m) slots cell :=
  ⟨assignmentOfMem m slots cell,memOfAssignment m⟩

theorem actualCellMember (m : Nat) (slots : List Slot) (ρ : Nat → Nat) (hm : 0 < m) :
    actualCell m slots ρ ∈ choices m slots := by
  apply memOfAssignment m
  induction slots with
  | nil => exact .nil
  | cons s ss ih => exact .cons (Nat.mod_lt _ (Nat.mul_pos (by decide) hm)) ih

end LogicLineages.PermittedControl.RankResidueChoices
