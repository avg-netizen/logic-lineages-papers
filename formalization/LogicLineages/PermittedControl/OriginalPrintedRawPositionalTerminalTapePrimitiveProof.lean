module
public import LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminalTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminal
attribute [local irreducible] Nat.sqrt Nat.unpair

private def children (code : Nat) : List Nat :=
  if code % 6 ≤ 2 then [] else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1,(code / 6).unpair.2]

private theorem childrenDecreasing : ∀ code child, child ∈ children code → child < code := by
  intro code child used
  by_cases leaf : code % 6 ≤ 2
  · simp [children,leaf] at used
  have hpos : 0 < code := by omega
  have hd := Nat.div_lt_self hpos (show 1 < 6 by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold children at used
  split_ifs at used <;> simp_all only [List.mem_cons,List.not_mem_nil,or_false]
  all_goals omega

private theorem tagPrimitive : Primrec (fun code : Nat => code % 6) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 6)

private theorem payloadPrimitive : Primrec (fun code : Nat => code / 6) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 6)

private theorem childrenPrimitive : Primrec children := by
  have left := Primrec.fst.comp (Primrec.unpair.comp payloadPrimitive)
  have right := Primrec.snd.comp (Primrec.unpair.comp payloadPrimitive)
  exact Primrec.ite (Primrec.nat_le.comp tagPrimitive (Primrec.const 2)) (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp tagPrimitive (Primrec.const 3))
      (Primrec.list_cons.comp payloadPrimitive (Primrec.const []))
      (Primrec.list_cons.comp left (Primrec.list_cons.comp right (Primrec.const []))))

private def assemble (code : Nat) (vals : List Tape) : Tape :=
  if code % 6 ≤ 2 then [code % 6]
  else if code % 6 = 3 then vals.getD 0 [] ++ [3]
  else vals.getD 0 [] ++ vals.getD 1 [] ++ [code % 6]

private theorem assembleEq (code : Nat) :
    tape code = assemble code ((children code).map tape) := by
  rw [tape]
  split_ifs <;> simp_all [assemble,children]

private theorem assemblePrimitive : Primrec₂ assemble := by
  let A := Nat × List Tape
  have tag : Primrec (fun p : A => p.1 % 6) := tagPrimitive.comp Primrec.fst
  have ls : Primrec (fun p : A => [p.1 % 6]) := Primrec.list_cons.comp tag (Primrec.const [])
  have c0 : Primrec (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : Tape)).comp Primrec.snd (Primrec.const 0)
  have c1 : Primrec (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : Tape)).comp Primrec.snd (Primrec.const 1)
  have last : Primrec (fun p : A => assemble p.1 p.2) :=
    Primrec.ite (Primrec.nat_le.comp tag (Primrec.const 2)) ls
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 3))
        (Primrec.list_append.comp c0 (Primrec.const [3]))
        (Primrec.list_append.comp (Primrec.list_append.comp c0 c1) ls))
  exact last.to₂

private def tapeStep (_ : Unit) (prior : List Tape) : Option Tape :=
  some (assemble prior.length ((children prior.length).map (fun k => prior.getD k [])))

private theorem tapeStepPrimitive : Primrec₂ tapeStep := by
  let A := Unit × List Tape
  have lookup : Primrec (fun p : A × Nat => p.1.2.getD p.2 []) :=
    (Primrec.list_getD ([] : Tape)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have n : Primrec (fun p : A => p.2.length) := Primrec.list_length.comp Primrec.snd
  have vals : Primrec (fun p : A => (children p.2.length).map (fun k => p.2.getD k [])) :=
    Primrec.list_map (childrenPrimitive.comp n) lookup.to₂
  exact Primrec.option_some.comp (assemblePrimitive.comp n vals)

theorem tapePrimitive : Primrec tape := by
  have h : Primrec₂ (fun (_ : Unit) code => tape code) := by
    apply Primrec.nat_strong_rec _ tapeStepPrimitive
    intro args code
    unfold tapeStep
    simp only [List.length_map,List.length_range]
    apply congrArg some
    rw [assembleEq code]
    apply congrArg (assemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := childrenDecreasing code i hi
    simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

end LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminal
