module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic.SplitIfs

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeProgramsProof
open LayeredComparison.IntegerAlgorithms.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem weighted_variable_primitive (c : Int) :
    Primrec (fun i : Nat => (c,i,([] : Word))) :=
  (Primrec.const c).pair (Primrec.id.pair (Primrec.const []))

theorem numeralRow_primitive : Primrec₂ numeralRow :=
  (negate_primitive.comp (ofNat_primitive.comp Primrec.snd)).pair
    (Primrec.list_cons.comp ((weighted_variable_primitive 1).comp Primrec.fst)
      (Primrec.const []))

theorem variableRow_primitive : Primrec₂ variableRow :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((weighted_variable_primitive 1).comp Primrec.fst)
      (Primrec.list_cons.comp ((weighted_variable_primitive (-1)).comp Primrec.snd)
        (Primrec.const [])))

theorem additionRow_primitive :
    Primrec (fun p : Nat × Nat × Nat => additionRow p.1 p.2.1 p.2.2) :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((weighted_variable_primitive 1).comp Primrec.fst)
      (Primrec.list_cons.comp
        ((weighted_variable_primitive (-1)).comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp
          ((weighted_variable_primitive (-1)).comp (Primrec.snd.comp Primrec.snd))
          (Primrec.const []))))

theorem scaleRow_primitive :
    Primrec (fun p : Nat × Nat × Nat => scaleRow p.1 p.2.1 p.2.2) :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((weighted_variable_primitive 1).comp Primrec.fst)
      (Primrec.list_cons.comp
        ((negate_primitive.comp (ofNat_primitive.comp
          (Primrec.fst.comp Primrec.snd))).pair
            ((Primrec.snd.comp Primrec.snd).pair (Primrec.const [])))
        (Primrec.const [])))

theorem emit_primitive :
    Primrec (fun p : ExpressionCode.State × (List Nat × Row) =>
      ExpressionCode.emit p.1 p.2.1 p.2.2) := by
  let A := ExpressionCode.State × (List Nat × Row)
  have hn : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp : Primrec (fun p : A => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact (Primrec.succ.comp hn).pair
    ((Primrec.list_cons.comp hn ht).pair
      (Primrec.list_append.comp hp
        (Primrec.list_cons.comp hr (Primrec.const []))))

theorem step_primitive : Primrec₂ ExpressionCode.step := by
  let A := ExpressionCode.State × Instruction
  have hs : Primrec (fun p : A => p.1) := Primrec.fst
  have hn : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun p : A => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have htag : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have harg : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have htop : Primrec (fun p : A => p.1.2.1.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp ht (Primrec.const 0)
  have hnext : Primrec (fun p : A => p.1.2.1.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp ht (Primrec.const 1)
  have hnum : Primrec (fun p : A =>
      ExpressionCode.emit p.1 p.1.2.1 (numeralRow p.1.1 p.2.2)) :=
    emit_primitive.comp (hs.pair (ht.pair (numeralRow_primitive.comp hn harg)))
  have hvar : Primrec (fun p : A =>
      ExpressionCode.emit p.1 p.1.2.1 (variableRow p.1.1 p.2.2)) :=
    emit_primitive.comp (hs.pair (ht.pair (variableRow_primitive.comp hn harg)))
  have hadd : Primrec (fun p : A =>
      ExpressionCode.emit p.1 (p.1.2.1.drop 2)
        (additionRow p.1.1 (p.1.2.1.getD 1 0) (p.1.2.1.getD 0 0))) :=
    emit_primitive.comp (hs.pair
      ((Primrec.list_drop.comp (Primrec.const 2) ht).pair
        (additionRow_primitive.comp (hn.pair (hnext.pair htop)))))
  have hscale : Primrec (fun p : A =>
      ExpressionCode.emit p.1 (p.1.2.1.drop 1)
        (scaleRow p.1.1 p.2.2 (p.1.2.1.getD 0 0))) :=
    emit_primitive.comp (hs.pair
      ((Primrec.list_drop.comp (Primrec.const 1) ht).pair
        (scaleRow_primitive.comp (hn.pair (harg.pair htop)))))
  have hcollapse : Primrec (fun p : A =>
      ExpressionCode.emit p.1 (p.1.2.1.drop 1)
        (headEquation p.2.2 (p.1.2.1.getD 0 0) p.1.1)) :=
    emit_primitive.comp (hs.pair
      ((Primrec.list_drop.comp (Primrec.const 1) ht).pair
        (HeadProgramsProof.headEquation_primitive.comp (harg.pair (htop.pair hn)))))
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hnum
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hvar
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hadd
        (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) hscale hcollapse)))

theorem run_primitive : Primrec₂ ExpressionCode.run := by
  have hs : Primrec
      (fun p : (List Instruction × ExpressionCode.State) × (ExpressionCode.State × Instruction) =>
        ExpressionCode.step p.2.1 p.2.2) :=
    step_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldl Primrec.fst Primrec.snd hs.to₂

private theorem selectedNames_primitive (tag : Nat) :
    Primrec (fun ops : List Instruction =>
      (ops.filter (fun op => decide (op.1 = tag))).map Prod.snd) := by
  let A := List Instruction × (Instruction × List Nat)
  have htag : Primrec (fun p : A => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have harg : Primrec (fun p : A => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have htail : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hs : Primrec (fun p : A =>
      if p.2.1.1 = tag then p.2.1.2 :: p.2.2 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp htag (Primrec.const tag))
      (Primrec.list_cons.comp harg htail) htail
  have hf : Primrec (fun ops : List Instruction =>
      ops.foldr (fun op tail => if op.1 = tag then op.2::tail else tail) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const []) hs.to₂
  apply hf.of_eq
  intro ops
  induction ops with
  | nil => rfl
  | cons op ops ih =>
      by_cases h : op.1 = tag <;> simp [List.foldr_cons, List.filter_cons, h, ih]

theorem originalNames_primitive : Primrec ExpressionCode.originalNames :=
  selectedNames_primitive 1

theorem headNames_primitive : Primrec ExpressionCode.headNames :=
  selectedNames_primitive 4

private theorem maxList_primitive : Primrec (fun xs : List Nat => xs.foldr max 0) :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem start_primitive : Primrec₂ ExpressionCode.start :=
  Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_max.comp Primrec.snd
      (maxList_primitive.comp (originalNames_primitive.comp Primrec.fst)))

theorem names_primitive : Primrec₂ names := by
  have hs : Primrec (fun p : (Nat × Nat) × Nat => p.1.1+p.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map (Primrec.list_range.comp Primrec.snd) hs.to₂

private def instructionChildren (code : Nat) : List Nat :=
  if code % 5 = 0 ∨ code % 5 = 1 then []
  else if code % 5 = 2 then [(code / 5).unpair.1, (code / 5).unpair.2]
  else [(code / 5).unpair.2]

private def instructionAssemble (code : Nat) (values : List (List Instruction)) :
    List Instruction :=
  if code % 5 = 0 then [(0, code / 5)]
  else if code % 5 = 1 then [(1, code / 5)]
  else if code % 5 = 2 then values.getD 0 [] ++ values.getD 1 [] ++ [(2, 0)]
  else if code % 5 = 3 then values.getD 0 [] ++ [(3, (code / 5).unpair.1)]
  else values.getD 0 [] ++ [(4, (code / 5).unpair.1)]

private theorem instruction_decreasing :
    ∀ code child, child ∈ instructionChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 5 = 0 ∨ code % 5 = 1
  · simp [instructionChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 5)
  have hr := Nat.unpair_right_le (code / 5)
  unfold instructionChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private theorem instruction_equation (code : Nat) :
    ExpressionCode.instructions code =
      instructionAssemble code ((instructionChildren code).map ExpressionCode.instructions) := by
  rw [ExpressionCode.instructions]
  split_ifs <;> simp_all [instructionChildren, instructionAssemble]

private theorem instruction_tag_primitive : Primrec (fun code : Nat => code % 5) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 5)
private theorem instruction_quotient_primitive : Primrec (fun code : Nat => code / 5) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 5)
private theorem instruction_tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 5 = n) :=
  Primrec.eq.comp instruction_tag_primitive (Primrec.const n)
private theorem instruction_left_primitive : Primrec (fun code : Nat => (code / 5).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp instruction_quotient_primitive)
private theorem instruction_right_primitive : Primrec (fun code : Nat => (code / 5).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp instruction_quotient_primitive)

private theorem instructionChildren_primitive : Primrec instructionChildren :=
  Primrec.ite ((instruction_tag_is 0).or (instruction_tag_is 1)) (Primrec.const [])
    (Primrec.ite (instruction_tag_is 2)
      (Primrec.list_cons.comp instruction_left_primitive
        (Primrec.list_cons.comp instruction_right_primitive (Primrec.const [])))
      (Primrec.list_cons.comp instruction_right_primitive (Primrec.const [])))

private theorem instructionAssemble_primitive : Primrec₂ instructionAssemble := by
  let A := Nat × List (List Instruction)
  have hq : Primrec (fun p : A => p.1 / 5) :=
    instruction_quotient_primitive.comp Primrec.fst
  have hleft : Primrec (fun p : A => (p.1 / 5).unpair.1) :=
    instruction_left_primitive.comp Primrec.fst
  have hzero : Primrec (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List Instruction)).comp Primrec.snd (Primrec.const 0)
  have hone : Primrec (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List Instruction)).comp Primrec.snd (Primrec.const 1)
  have hnum : Primrec (fun p : A => [(0, p.1 / 5)]) :=
    Primrec.list_cons.comp ((Primrec.const 0).pair hq) (Primrec.const [])
  have hvar : Primrec (fun p : A => [(1, p.1 / 5)]) :=
    Primrec.list_cons.comp ((Primrec.const 1).pair hq) (Primrec.const [])
  have hadd : Primrec (fun p : A => p.2.getD 0 [] ++ p.2.getD 1 [] ++ [(2, 0)]) :=
    Primrec.list_append.comp (Primrec.list_append.comp hzero hone) (Primrec.const [(2, 0)])
  have hscale : Primrec (fun p : A => p.2.getD 0 [] ++ [(3, (p.1 / 5).unpair.1)]) :=
    Primrec.list_append.comp hzero
      (Primrec.list_cons.comp ((Primrec.const 3).pair hleft) (Primrec.const []))
  have hcollapse : Primrec (fun p : A => p.2.getD 0 [] ++ [(4, (p.1 / 5).unpair.1)]) :=
    Primrec.list_append.comp hzero
      (Primrec.list_cons.comp ((Primrec.const 4).pair hleft) (Primrec.const []))
  exact Primrec.ite ((instruction_tag_is 0).comp Primrec.fst) hnum
    (Primrec.ite ((instruction_tag_is 1).comp Primrec.fst) hvar
      (Primrec.ite ((instruction_tag_is 2).comp Primrec.fst) hadd
        (Primrec.ite ((instruction_tag_is 3).comp Primrec.fst) hscale hcollapse)))

private def instructionStep (values : List (List Instruction)) : Option (List Instruction) :=
  some (instructionAssemble values.length
    ((instructionChildren values.length).map (fun i => values.getD i [])))

private theorem instructionStep_primitive : Primrec instructionStep := by
  have hs : Primrec (fun p : List (List Instruction) × Nat => p.1.getD p.2 []) :=
    (Primrec.list_getD ([] : List Instruction)).comp Primrec.fst Primrec.snd
  have hm : Primrec (fun values : List (List Instruction) =>
      (instructionChildren values.length).map (fun i => values.getD i [])) :=
    Primrec.list_map (instructionChildren_primitive.comp Primrec.list_length) hs.to₂
  exact Primrec.option_some.comp
    (instructionAssemble_primitive.comp Primrec.list_length hm)

/-- Course-of-values recursion computes the literal radix-5 instructions.
Only proper expression children enter the recursion table; head codes and
arithmetic coefficients are copied as finite syntax. -/
theorem instructions_primitive : Primrec ExpressionCode.instructions := by
  have h : Primrec₂ (fun (_ : Unit) (code : Nat) => ExpressionCode.instructions code) := by
    apply Primrec.nat_strong_rec _ (instructionStep_primitive.comp Primrec.snd).to₂
    intro _ code
    unfold instructionStep
    simp only [List.length_map, List.length_range]
    apply congrArg some
    rw [instruction_equation code]
    apply congrArg (instructionAssemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := instruction_decreasing code i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

theorem package_primitive : Primrec₂ ExpressionCode.package := by
  have hops : Primrec (fun p : Nat × Nat => ExpressionCode.instructions p.1) :=
    instructions_primitive.comp Primrec.fst
  have hstart : Primrec (fun p : Nat × Nat =>
      ExpressionCode.start (ExpressionCode.instructions p.1) p.2) :=
    start_primitive.comp hops Primrec.snd
  have hs : Primrec (fun p : Nat × Nat =>
      ExpressionCode.run (ExpressionCode.instructions p.1)
        (ExpressionCode.start (ExpressionCode.instructions p.1) p.2,[],[])) :=
    run_primitive.comp hops
      (hstart.pair ((Primrec.const []).pair (Primrec.const [])))
  have hnames : Primrec (fun p : Nat × Nat =>
      names (ExpressionCode.start (ExpressionCode.instructions p.1) p.2)
        (ExpressionCode.instructions p.1).length) :=
    names_primitive.comp hstart (Primrec.list_length.comp hops)
  have hresult : Primrec (fun p : Nat × Nat =>
      variableRow p.2
        ((ExpressionCode.run (ExpressionCode.instructions p.1)
          (ExpressionCode.start (ExpressionCode.instructions p.1) p.2,[],[])).1-1)) :=
    variableRow_primitive.comp Primrec.snd
      (Primrec.nat_sub.comp (Primrec.fst.comp hs) (Primrec.const 1))
  exact (HeadProgramsProof.familyDegree_primitive.comp
    (headNames_primitive.comp hops)).pair
      (hnames.pair (Primrec.list_append.comp
        (Primrec.snd.comp (Primrec.snd.comp hs))
        (Primrec.list_cons.comp hresult (Primrec.const []))))

theorem actualNumericProgram : ExpressionTargets.ActualNumericProgram :=
  ⟨instructions_primitive,run_primitive,package_primitive⟩

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeProgramsProof
