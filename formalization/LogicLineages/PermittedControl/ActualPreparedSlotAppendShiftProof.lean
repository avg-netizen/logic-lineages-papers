module
public import LogicLineages.PermittedControl.ActualPreparedSlotAppendTargets
import LogicLineages.PermittedControl.PreparedParameterRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPreparedSlotAppend
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open NormalForm PreparedProjection

private theorem nameShift (d : Nat) (s : Summand) : (shiftSummand d s).name = shiftName d s.name := by
  cases s <;> rfl

private theorem rowVariablesShift (d : Nat) (r : Row) :
    rowVariables (shiftRow d r) = (rowVariables r).map (shiftName d) := by
  simp only [rowVariables,shiftRow,List.map_map,Function.comp_def,nameShift]

private theorem atomVariablesShift (d : Nat) (a : Atom) :
    (Formula.atom (shiftAtom d a)).variables = (Formula.atom a).variables.map (shiftName d) := by
  cases a <;> exact rowVariablesShift d _

private theorem variablesShift (d : Nat) (p : Formula) :
    (shift d p).variables = p.variables.map (shiftName d) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact atomVariablesShift d a
  | negative p ih => exact ih
  | conjunction p q hp hq => simp only [shift,Formula.variables,List.map_append,hp,hq]
  | disjunction p q hp hq => simp only [shift,Formula.variables,List.map_append,hp,hq]

private theorem atomsShift (d : Nat) (p : Formula) :
    LinearRows.atoms (shift d p) = (LinearRows.atoms p).map (shiftAtom d) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => rfl
  | negative p ih => exact ih
  | conjunction p q hp hq => simp only [shift,LinearRows.atoms,List.map_append,hp,hq]
  | disjunction p q hp hq => simp only [shift,LinearRows.atoms,List.map_append,hp,hq]

private theorem rowShiftPlain (d : Nat) (r : Row) (h : PlainPreparedRow r) :
    PlainPreparedRow (shiftRow d r) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  obtain ⟨i,eq⟩ := h s hs
  exact ⟨shiftName d i,by change shiftSummand d s.2 = _; rw [eq] <;> rfl⟩

private theorem shiftedPlain (d : Nat) (p : Formula) (h : PlainPreparedFormula p) :
    PlainPreparedFormula (shift d p) := by
  intro a ha
  rw [atomsShift] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  have row := h b hb
  cases b <;> exact rowShiftPlain d _ row

private theorem rowShiftValue (d : Nat) (r : Row) (h : PlainPreparedRow r) (ν : Nat → Nat) :
    rowValue (shiftRow d r) ν = rowValue r (view d ν) := by
  have terms :
      r.2.map (fun t => t.1 * ((shiftSummand d t.2).term.value ν : Int)) =
        r.2.map (fun t => t.1 * (t.2.term.value (view d ν) : Int)) := by
    apply List.map_congr_left
    intro t ht
    obtain ⟨i,eq⟩ := h t ht
    rw [eq] <;> rfl
  simp only [rowValue,shiftRow,List.map_map,Function.comp_def,terms]

private theorem atomShiftMeaning (d : Nat) (a : Atom) (h : PlainPreparedRow a.row) (ν : Nat → Nat) :
    (shiftAtom d a).eval ν ↔ a.eval (view d ν) := by
  cases a with
  | nonnegative r =>
      change (0 ≤ rowValue (shiftRow d r) ν ↔ 0 ≤ rowValue r (view d ν))
      rw [rowShiftValue d r h ν]
  | divisible m r =>
      change (((m+1 : Nat) : Int) ∣ rowValue (shiftRow d r) ν) ↔
        ((m+1 : Nat) : Int) ∣ rowValue r (view d ν)
      rw [rowShiftValue d r h ν]

private theorem shiftMeaning (d : Nat) (p : Formula) (plain : PlainPreparedFormula p) (ν : Nat → Nat) :
    (shift d p).eval ν ↔ p.eval (view d ν) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact atomShiftMeaning d a (plain a List.mem_cons_self) ν
  | negative p ih => exact not_congr (ih plain)
  | conjunction p q hp hq =>
      exact and_congr (hp (fun a ha => plain a (List.mem_append_left _ ha)))
        (hq (fun a ha => plain a (List.mem_append_right _ ha)))
  | disjunction p q hp hq =>
      exact or_congr (hp (fun a ha => plain a (List.mem_append_left _ ha)))
        (hq (fun a ha => plain a (List.mem_append_right _ ha)))

theorem exactSlotShift : ExactSlotShift :=
  ⟨fun _ _ => rfl,fun d p => ⟨variablesShift d p,fun plain =>
    ⟨shiftedPlain d p plain,shiftMeaning d p plain⟩⟩⟩

end LogicLineages.PermittedControl.ActualPreparedSlotAppend
