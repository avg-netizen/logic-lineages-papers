module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic.SplitIfs

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof
open SourceTermGraph
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem variableData_primitive : Primrec Code.variableData :=
  (Primrec.const 0).pair (Primrec.id.pair
    ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))
theorem phiData_primitive : Primrec Code.phiData :=
  (Primrec.const 1).pair (Primrec.id.pair
    ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))

private theorem weighted_variable_primitive (c : Int) :
    Primrec (fun i : Nat => (c, Code.variableData i)) :=
  (Primrec.const c).pair variableData_primitive

theorem numeralRow_primitive : Primrec₂ Code.numeralRow :=
  (IntegerAlgorithms.Proof.negate_primitive.comp
    (IntegerAlgorithms.Proof.ofNat_primitive.comp Primrec.snd)).pair
    (Primrec.list_cons.comp ((weighted_variable_primitive 1).comp Primrec.fst)
      (Primrec.const []))

theorem variableRow_primitive : Primrec₂ Code.variableRow :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((weighted_variable_primitive 1).comp Primrec.fst)
      (Primrec.list_cons.comp ((weighted_variable_primitive (-1)).comp Primrec.snd)
        (Primrec.const [])))

theorem additionRow_primitive :
    Primrec (fun p : Nat × (Nat × Nat) => Code.additionRow p.1 p.2.1 p.2.2) :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((weighted_variable_primitive 1).comp Primrec.fst)
      (Primrec.list_cons.comp
        ((weighted_variable_primitive (-1)).comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp
          ((weighted_variable_primitive (-1)).comp (Primrec.snd.comp Primrec.snd))
          (Primrec.const []))))

theorem phiRow_primitive : Primrec₂ Code.phiRow :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((weighted_variable_primitive 1).comp Primrec.fst)
      (Primrec.list_cons.comp
        ((Primrec.const (-1 : Int)).pair (phiData_primitive.comp Primrec.snd))
        (Primrec.const [])))

theorem negateRow_primitive : Primrec Code.negateRow := by
  let Item := Int × NormalForm.Code.ItemData
  have hs : Primrec (fun p : Code.RowData × Item => (-p.2.1, p.2.2)) :=
    (IntegerAlgorithms.Proof.negate_primitive.comp
      (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  exact (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.fst).pair
    (Primrec.list_map Primrec.snd hs.to₂)

theorem atom_primitive : Primrec Code.atom := by
  have hp : Primrec (fun row : Code.RowData =>
      ((0, 0, row) : NormalForm.Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id)
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp hp))
    (Primrec.const 2)

theorem conjunction_primitive : Primrec₂ Code.conjunction :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 4)

theorem equation_primitive : Primrec Code.equation :=
  conjunction_primitive.comp atom_primitive (atom_primitive.comp negateRow_primitive)

theorem equations_primitive : Primrec Code.equations := by
  have hs : Primrec (fun p : List Code.RowData × (Code.RowData × Nat) =>
      Code.conjunction (Code.equation p.2.1) p.2.2) :=
    conjunction_primitive.comp
      (equation_primitive.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hs.to₂

theorem emit_primitive :
    Primrec (fun p : Code.State × (List Nat × Code.RowData) =>
      Code.emit p.1 p.2.1 p.2.2) := by
  let A := Code.State × (List Nat × Code.RowData)
  have hn : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp : Primrec (fun p : A => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact (Primrec.succ.comp hn).pair
    ((Primrec.list_cons.comp hn ht).pair
      (Primrec.list_append.comp hp
        (Primrec.list_cons.comp hr (Primrec.const []))))

theorem step_primitive : Primrec₂ Code.step := by
  let A := Code.State × Instruction
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
      Code.emit p.1 p.1.2.1 (Code.numeralRow p.1.1 p.2.2)) :=
    emit_primitive.comp (hs.pair (ht.pair (numeralRow_primitive.comp hn harg)))
  have hvar : Primrec (fun p : A =>
      Code.emit p.1 p.1.2.1 (Code.variableRow p.1.1 p.2.2)) :=
    emit_primitive.comp (hs.pair (ht.pair (variableRow_primitive.comp hn harg)))
  have hadd : Primrec (fun p : A =>
      Code.emit p.1 (p.1.2.1.drop 2)
        (Code.additionRow p.1.1 (p.1.2.1.getD 1 0) (p.1.2.1.getD 0 0))) :=
    emit_primitive.comp (hs.pair
      ((Primrec.list_drop.comp (Primrec.const 2) ht).pair
        (additionRow_primitive.comp (hn.pair (hnext.pair htop)))))
  have hphi : Primrec (fun p : A =>
      Code.emit p.1 (p.1.2.1.drop 1) (Code.phiRow p.1.1 (p.1.2.1.getD 0 0))) :=
    emit_primitive.comp (hs.pair
      ((Primrec.list_drop.comp (Primrec.const 1) ht).pair
        (phiRow_primitive.comp hn htop)))
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hnum
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hvar
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hadd hphi))

theorem run_primitive : Primrec₂ Code.run := by
  have hs : Primrec (fun p : (List Instruction × Code.State) × (Code.State × Instruction) =>
      Code.step p.2.1 p.2.2) :=
    step_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldl Primrec.fst Primrec.snd hs.to₂

private def instructionChildren (code : Nat) : List Nat :=
  if code % 4 = 0 ∨ code % 4 = 1 then []
  else if code % 4 = 2 then [(code / 4).unpair.1, (code / 4).unpair.2]
  else [code / 4]

private def instructionAssemble (code : Nat) (values : List (List Instruction)) :
    List Instruction :=
  if code % 4 = 0 then [(0, code / 4)]
  else if code % 4 = 1 then [(1, code / 4)]
  else if code % 4 = 2 then values.getD 0 [] ++ values.getD 1 [] ++ [(2, 0)]
  else values.getD 0 [] ++ [(3, 0)]

private theorem instruction_decreasing :
    ∀ code child, child ∈ instructionChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 4 = 0 ∨ code % 4 = 1
  · simp [instructionChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 4)
  have hr := Nat.unpair_right_le (code / 4)
  unfold instructionChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private theorem instruction_equation (code : Nat) :
    Code.instructions code =
      instructionAssemble code ((instructionChildren code).map Code.instructions) := by
  rw [Code.instructions]
  split_ifs <;> simp_all [instructionChildren, instructionAssemble]

private theorem instruction_tag_primitive : Primrec (fun code : Nat => code % 4) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
private theorem instruction_quotient_primitive : Primrec (fun code : Nat => code / 4) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 4)
private theorem instruction_tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 4 = n) :=
  Primrec.eq.comp instruction_tag_primitive (Primrec.const n)
private theorem instruction_left_primitive : Primrec (fun code : Nat => (code / 4).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp instruction_quotient_primitive)
private theorem instruction_right_primitive : Primrec (fun code : Nat => (code / 4).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp instruction_quotient_primitive)

private theorem instructionChildren_primitive : Primrec instructionChildren :=
  Primrec.ite ((instruction_tag_is 0).or (instruction_tag_is 1)) (Primrec.const [])
    (Primrec.ite (instruction_tag_is 2)
      (Primrec.list_cons.comp instruction_left_primitive
        (Primrec.list_cons.comp instruction_right_primitive (Primrec.const [])))
      (Primrec.list_cons.comp instruction_quotient_primitive (Primrec.const [])))

private theorem instructionAssemble_primitive : Primrec₂ instructionAssemble := by
  let A := Nat × List (List Instruction)
  have hq : Primrec (fun p : A => p.1 / 4) :=
    instruction_quotient_primitive.comp Primrec.fst
  have hzero : Primrec (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List Instruction)).comp Primrec.snd (Primrec.const 0)
  have hone : Primrec (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List Instruction)).comp Primrec.snd (Primrec.const 1)
  have hnum : Primrec (fun p : A => [(0, p.1 / 4)]) :=
    Primrec.list_cons.comp ((Primrec.const 0).pair hq) (Primrec.const [])
  have hvar : Primrec (fun p : A => [(1, p.1 / 4)]) :=
    Primrec.list_cons.comp ((Primrec.const 1).pair hq) (Primrec.const [])
  have hadd : Primrec (fun p : A => p.2.getD 0 [] ++ p.2.getD 1 [] ++ [(2, 0)]) :=
    Primrec.list_append.comp (Primrec.list_append.comp hzero hone) (Primrec.const [(2, 0)])
  have hphi : Primrec (fun p : A => p.2.getD 0 [] ++ [(3, 0)]) :=
    Primrec.list_append.comp hzero (Primrec.const [(3, 0)])
  exact Primrec.ite ((instruction_tag_is 0).comp Primrec.fst) hnum
    (Primrec.ite ((instruction_tag_is 1).comp Primrec.fst) hvar
      (Primrec.ite ((instruction_tag_is 2).comp Primrec.fst) hadd hphi))

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

/-- Primitive course-of-values recursion computes the literal radix-4
instruction list; the recursion table contains only strictly smaller codes. -/
theorem instructions_primitive : Primrec Code.instructions := by
  have h : Primrec₂ (fun (_ : Unit) (code : Nat) => Code.instructions code) := by
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

theorem package_primitive : Primrec₂ Code.package := by
  have hs : Primrec (fun p : Nat × Nat =>
      Code.run (Code.instructions p.1) (p.2, [], [])) :=
    run_primitive.comp (instructions_primitive.comp Primrec.fst)
      (Primrec.snd.pair ((Primrec.const []).pair (Primrec.const [])))
  exact Primrec.encode.comp
    ((Primrec.nat_sub.comp (Primrec.fst.comp hs) (Primrec.const 1)).pair
      (equations_primitive.comp (Primrec.snd.comp (Primrec.snd.comp hs))))

theorem actualNumericProgram : SourceTermGraphTargets.ActualNumericProgram :=
  ⟨instructions_primitive, run_primitive, package_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof
