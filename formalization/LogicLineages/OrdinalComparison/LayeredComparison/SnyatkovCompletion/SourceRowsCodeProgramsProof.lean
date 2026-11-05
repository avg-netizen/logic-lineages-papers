module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProof
open SourceRows
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem binary_primitive (base tag : Nat) :
    Primrec₂ (fun a b : Nat => base * Nat.pair a b + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair)
    (Primrec.const tag)
private theorem unary_primitive (base tag : Nat) :
    Primrec (fun a : Nat => base * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec.id)
    (Primrec.const tag)

theorem opBound_primitive : Primrec Code.opBound :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
    (Primrec.succ.comp Primrec.snd) (Primrec.const 0)

theorem bound_primitive : Primrec Code.bound := by
  have hm : Primrec (fun ops : List SourceTermGraph.Instruction => ops.map Code.opBound) :=
    Primrec.list_map Primrec.id (opBound_primitive.comp Primrec.snd).to₂
  have hs : Primrec (fun p : List SourceTermGraph.Instruction × (Nat × Nat) =>
      max p.2.1 p.2.2) :=
    Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr hm (Primrec.const 0) hs.to₂

theorem names_primitive : Primrec₂ SourceTermGraph.names := by
  have hs : Primrec (fun p : (Nat × Nat) × Nat => p.1.1 + p.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map (Primrec.list_range.comp Primrec.snd) hs.to₂

theorem bindAll_primitive : Primrec₂ Code.bindAll := by
  have hs : Primrec (fun p : (List Nat × Nat) × (Nat × Nat) =>
      4 * Nat.pair p.2.1 p.2.2 + 3) :=
    (binary_primitive 4 3).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.fst Primrec.snd hs.to₂

theorem strictRow_primitive : Primrec₂ Code.strictRow :=
  (Primrec.const (-1 : Int)).pair
    (Primrec.list_cons.comp
      ((Primrec.const (1 : Int)).pair
        (SourceTermGraphCodeProof.variableData_primitive.comp Primrec.snd))
      (Primrec.list_cons.comp
        ((Primrec.const (-1 : Int)).pair
          (SourceTermGraphCodeProof.variableData_primitive.comp Primrec.fst))
        (Primrec.const [])))

theorem relation_primitive :
    Primrec (fun p : Bool × (Nat × Nat) => Code.relation p.1 p.2.1 p.2.2) :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true))
    (SourceTermGraphCodeProof.atom_primitive.comp
      (strictRow_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
    (SourceTermGraphCodeProof.equation_primitive.comp
      (SourceTermGraphCodeProof.variableRow_primitive.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

/-- Every numeric atom component is computed from the actual two source term
codes: local fresh bound, postfix graph, output indices, rows, and binders. -/
theorem atom_primitive :
    Primrec (fun p : Bool × (Nat × Nat) => Code.atom p.1 p.2.1 p.2.2) := by
  let A := Bool × (Nat × Nat)
  have ha : Primrec (fun p : A => SourceTermGraph.Code.instructions p.2.1) :=
    SourceTermGraphCodeProof.instructions_primitive.comp (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : A => SourceTermGraph.Code.instructions p.2.2) :=
    SourceTermGraphCodeProof.instructions_primitive.comp (Primrec.snd.comp Primrec.snd)
  have hstart : Primrec (fun p : A =>
      max (Code.bound (SourceTermGraph.Code.instructions p.2.1))
        (Code.bound (SourceTermGraph.Code.instructions p.2.2))) :=
    Primrec.nat_max.comp (bound_primitive.comp ha) (bound_primitive.comp hb)
  have hca : Primrec (fun p : A => (SourceTermGraph.Code.instructions p.2.1).length) :=
    Primrec.list_length.comp ha
  have hcb : Primrec (fun p : A => (SourceTermGraph.Code.instructions p.2.2).length) :=
    Primrec.list_length.comp hb
  have hjoin : Primrec (fun p : A => 4 * Nat.pair p.2.1 p.2.2 + 2) :=
    (binary_primitive 4 2).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : A =>
      SourceTermGraph.Code.run
        (SourceTermGraph.Code.instructions (4 * Nat.pair p.2.1 p.2.2 + 2))
        (max (Code.bound (SourceTermGraph.Code.instructions p.2.1))
          (Code.bound (SourceTermGraph.Code.instructions p.2.2)), [], [])) :=
    SourceTermGraphCodeProof.run_primitive.comp
      (SourceTermGraphCodeProof.instructions_primitive.comp hjoin)
      (hstart.pair ((Primrec.const []).pair (Primrec.const [])))
  have hleft := Primrec.nat_sub.comp (Primrec.nat_add.comp hstart hca) (Primrec.const 1)
  have hright := Primrec.nat_sub.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp hstart hca) hcb) (Primrec.const 1)
  have hrelation := relation_primitive.comp (Primrec.fst.pair (hleft.pair hright))
  have hrows := SourceTermGraphCodeProof.equations_primitive.comp
    (Primrec.snd.comp (Primrec.snd.comp hs))
  have hbody := SourceTermGraphCodeProof.conjunction_primitive.comp hrows hrelation
  have hcount := Primrec.succ.comp (Primrec.nat_add.comp hca hcb)
  exact bindAll_primitive.comp (names_primitive.comp hstart hcount)
    (Primrec.nat_mul.comp (Primrec.const 4) hbody)

attribute [local irreducible] Code.atom

private theorem atom_false_primitive : Primrec₂ (Code.atom false) := by
  have hp : Primrec (fun p : Nat × Nat => (false, p)) :=
    (Primrec.const false).pair Primrec.id
  exact atom_primitive.comp hp
private theorem atom_true_primitive : Primrec₂ (Code.atom true) := by
  have hp : Primrec (fun p : Nat × Nat => (true, p)) :=
    (Primrec.const true).pair Primrec.id
  exact atom_primitive.comp hp

private def translateChildren (code : Nat) : List Nat :=
  if code % 5 = 0 ∨ code % 5 = 1 then []
  else if code % 5 = 2 then [code / 5]
  else if code % 5 = 3 then [(code / 5).unpair.1, (code / 5).unpair.2]
  else [(code / 5).unpair.2]

private def translateAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 5 = 0 then Code.atom false (code / 5).unpair.1 (code / 5).unpair.2
  else if code % 5 = 1 then Code.atom true (code / 5).unpair.1 (code / 5).unpair.2
  else if code % 5 = 2 then 4 * values.getD 0 0 + 1
  else if code % 5 = 3 then 4 * Nat.pair (values.getD 0 0) (values.getD 1 0) + 2
  else 4 * Nat.pair (code / 5).unpair.1 (values.getD 0 0) + 3

private theorem translate_decreasing :
    ∀ code child, child ∈ translateChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 5 = 0 ∨ code % 5 = 1
  · simp [translateChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 5)
  have hr := Nat.unpair_right_le (code / 5)
  unfold translateChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private theorem translate_equation (code : Nat) :
    Code.translate code = translateAssemble code ((translateChildren code).map Code.translate) := by
  rw [Code.translate]
  split_ifs <;> simp_all [translateChildren, translateAssemble]

private theorem tag_primitive : Primrec (fun code : Nat => code % 5) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 5)
private theorem quotient_primitive : Primrec (fun code : Nat => code / 5) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 5)
private theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 5 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
private theorem left_primitive : Primrec (fun code : Nat => (code / 5).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
private theorem right_primitive : Primrec (fun code : Nat => (code / 5).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)

private theorem translateChildren_primitive : Primrec translateChildren :=
  Primrec.ite ((tag_is 0).or (tag_is 1)) (Primrec.const [])
    (Primrec.ite (tag_is 2)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.ite (tag_is 3)
        (Primrec.list_cons.comp left_primitive
          (Primrec.list_cons.comp right_primitive (Primrec.const [])))
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private theorem translateAssemble_primitive : Primrec₂ translateAssemble := by
  let A := Nat × List Nat
  have hleft : Primrec (fun p : A => (p.1 / 5).unpair.1) :=
    left_primitive.comp Primrec.fst
  have hright : Primrec (fun p : A => (p.1 / 5).unpair.2) :=
    right_primitive.comp Primrec.fst
  have hzero : Primrec (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have hone : Primrec (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite ((tag_is 0).comp Primrec.fst)
    (atom_false_primitive.comp hleft hright)
    (Primrec.ite ((tag_is 1).comp Primrec.fst)
      (atom_true_primitive.comp hleft hright)
      (Primrec.ite ((tag_is 2).comp Primrec.fst)
        ((unary_primitive 4 1).comp hzero)
        (Primrec.ite ((tag_is 3).comp Primrec.fst)
          ((binary_primitive 4 2).comp hzero hone)
          ((binary_primitive 4 3).comp hleft hzero))))

private def translateStep (values : List Nat) : Option Nat :=
  some (translateAssemble values.length
    ((translateChildren values.length).map (fun i => values.getD i 0)))

private theorem translateStep_primitive : Primrec translateStep := by
  have hs : Primrec (fun p : List Nat × Nat => p.1.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.fst Primrec.snd
  have hm : Primrec (fun values : List Nat =>
      (translateChildren values.length).map (fun i => values.getD i 0)) :=
    Primrec.list_map (translateChildren_primitive.comp Primrec.list_length) hs.to₂
  exact Primrec.option_some.comp (translateAssemble_primitive.comp Primrec.list_length hm)

/-- The all-code compiler is primitive recursive on the actual source radix-5
syntax, with the original binder name copied into every existential branch. -/
theorem translate_primitive : Primrec Code.translate := by
  have h : Primrec₂ (fun (_ : Unit) (code : Nat) => Code.translate code) := by
    apply Primrec.nat_strong_rec _ (translateStep_primitive.comp Primrec.snd).to₂
    intro _ code
    unfold translateStep
    simp only [List.length_map, List.length_range]
    apply congrArg some
    rw [translate_equation code]
    apply congrArg (translateAssemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := translate_decreasing code i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

theorem actualSourceNumericProgram : SourceRowsTargets.ActualSourceNumericProgram :=
  translate_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProof
