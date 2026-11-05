module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDataProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsProof
open MaximalPlainBranchPrograms
attribute [local irreducible] Nat.sqrt Nat.unpair
attribute [local irreducible] LinearRows.Code.decodeAtom MaximalPlainPrograms.Code.compileAtom

private def children (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1, (code / 6).unpair.2]

private def assemble (i code : Nat) (values : List Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then MaximalPlainPrograms.Code.compileAtom i (LinearRows.Code.decodeAtom (code / 6))
  else if code % 6 = 3 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + code % 6

private theorem children_decreasing : ∀ code child, child ∈ children code → child < code := by
  intro code child h
  by_cases hleaf : code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2
  · simp [children, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold children at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private theorem compile_equation (i code : Nat) :
    Code.compile i code = assemble i code ((children code).map (Code.compile i)) := by
  rw [Code.compile]
  split_ifs <;> simp_all [children, assemble]

private theorem tag_primitive : Primrec (fun code : Nat => code % 6) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 6)
private theorem quotient_primitive : Primrec (fun code : Nat => code / 6) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 6)
private theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 6 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
private theorem left_primitive : Primrec (fun code : Nat => (code / 6).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
private theorem right_primitive : Primrec (fun code : Nat => (code / 6).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
private theorem children_primitive : Primrec children :=
  Primrec.ite ((tag_is 0).or ((tag_is 1).or (tag_is 2))) (Primrec.const [])
    (Primrec.ite (tag_is 3)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp left_primitive (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private theorem assemble_primitive :
    Primrec (fun p : Nat × (Nat × List Nat) => assemble p.1 p.2.1 p.2.2) := by
  let A := Nat × (Nat × List Nat)
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have h0 : Primrec (fun p : A => p.2.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 1)
  have ha : Primrec (fun p : A =>
      MaximalPlainPrograms.Code.compileAtom p.1 (LinearRows.Code.decodeAtom (p.2.1 / 6))) :=
    MaximalPlainProgramsProof.compileAtom_primitive.comp Primrec.fst
      (LinearRowsCodeProof.decodeAtom_primitive.comp (quotient_primitive.comp hc))
  have hn : Primrec (fun p : A => 6 * p.2.2.getD 0 0 + 3) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) h0) (Primrec.const 3)
  have hb : Primrec (fun p : A =>
      6 * Nat.pair (p.2.2.getD 0 0) (p.2.2.getD 1 0) + p.2.1 % 6) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp h0 h1)) (tag_primitive.comp hc)
  exact Primrec.ite ((tag_is 0).comp hc) (Primrec.const 0)
    (Primrec.ite ((tag_is 1).comp hc) (Primrec.const 1)
      (Primrec.ite ((tag_is 2).comp hc) ha
        (Primrec.ite ((tag_is 3).comp hc) hn hb)))

private def step (i : Nat) (values : List Nat) : Option Nat :=
  some (assemble i values.length ((children values.length).map (fun k => values.getD k 0)))

private theorem step_primitive : Primrec₂ step := by
  let A := Nat × List Nat
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A => (children p.2.length).map (fun k => p.2.getD k 0)) :=
    Primrec.list_map (children_primitive.comp (Primrec.list_length.comp Primrec.snd)) hs.to₂
  have hp : Primrec (fun p : A =>
      (p.1, p.2.length, (children p.2.length).map (fun k => p.2.getD k 0))) :=
    Primrec.fst.pair ((Primrec.list_length.comp Primrec.snd).pair hm)
  exact Primrec.option_some.comp (assemble_primitive.comp hp)

theorem compile_primitive : Primrec₂ Code.compile := by
  apply Primrec.nat_strong_rec _ step_primitive
  intro i code
  unfold step
  simp only [List.length_map, List.length_range]
  apply congrArg some
  rw [compile_equation i code]
  apply congrArg (assemble i code)
  apply List.map_congr_left
  intro k hk
  have hlt := children_decreasing code k hk
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]

attribute [local irreducible] Code.frame

theorem framed_primitive : Primrec₂ Code.framed :=
  ShiftedInputProgramsProof.conjunction_primitive.comp frame_primitive compile_primitive

attribute [local irreducible] Code.framed

theorem eliminate_primitive : Primrec₂ Code.eliminate :=
  LinearRowsCodeProof.eliminate_primitive.comp Primrec.fst framed_primitive

theorem actualBranchPrograms : MaximalPlainBranchProgramsTargets.ActualBranchPrograms :=
  ⟨compile_primitive, framed_primitive, eliminate_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsProof
