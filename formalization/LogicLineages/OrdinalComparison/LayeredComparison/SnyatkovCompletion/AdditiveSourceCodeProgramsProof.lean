module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceProof
open AdditiveSource
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem termTest_primitive : Primrec Code.termTest := by
  have hp : Primrec₂ (fun (_ : Unit) (op : SourceTermGraph.Instruction) => op.1 != 3) := by
    apply ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 3)).not.decide).of_eq
    intro p
    by_cases h : p.2.1 = 3 <;> simp [h]
  exact (LinearRowsCodeProof.listAll_primitive hp).comp
    (Primrec.const ()) SourceTermGraphCodeProof.instructions_primitive

private def children (code : Nat) : List Nat :=
  if code % 5 = 0 ∨ code % 5 = 1 then []
  else if code % 5 = 2 then [code / 5]
  else if code % 5 = 3 then [(code / 5).unpair.1, (code / 5).unpair.2]
  else [(code / 5).unpair.2]

private theorem children_decreasing : ∀ code child, child ∈ children code → child < code := by
  intro code child h
  by_cases hleaf : code % 5 = 0 ∨ code % 5 = 1
  · simp [children, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 5)
  have hr := Nat.unpair_right_le (code / 5)
  unfold children at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private def assemble (code : Nat) (values : List Bool) : Bool :=
  if code % 5 = 0 ∨ code % 5 = 1 then
    Code.termTest (code / 5).unpair.1 && Code.termTest (code / 5).unpair.2
  else if code % 5 = 2 then values.getD 0 false
  else if code % 5 = 3 then values.getD 0 false && values.getD 1 false
  else values.getD 0 false

private theorem test_equation (code : Nat) :
    Code.test code = assemble code ((children code).map Code.test) := by
  rw [Code.test]
  split_ifs <;> simp_all [children, assemble]

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
private theorem children_primitive : Primrec children :=
  Primrec.ite ((tag_is 0).or (tag_is 1)) (Primrec.const [])
    (Primrec.ite (tag_is 2)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.ite (tag_is 3)
        (Primrec.list_cons.comp left_primitive
          (Primrec.list_cons.comp right_primitive (Primrec.const [])))
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private theorem assemble_primitive : Primrec₂ assemble := by
  let A := Nat × List Bool
  have h0 : Primrec (fun p : A => p.2.getD 0 false) :=
    (Primrec.list_getD false).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 false) :=
    (Primrec.list_getD false).comp Primrec.snd (Primrec.const 1)
  have ha : Primrec (fun p : A =>
      Code.termTest (p.1 / 5).unpair.1 && Code.termTest (p.1 / 5).unpair.2) :=
    Primrec.and.comp (termTest_primitive.comp (left_primitive.comp Primrec.fst))
      (termTest_primitive.comp (right_primitive.comp Primrec.fst))
  exact Primrec.ite (((tag_is 0).or (tag_is 1)).comp Primrec.fst) ha
    (Primrec.ite ((tag_is 2).comp Primrec.fst) h0
      (Primrec.ite ((tag_is 3).comp Primrec.fst) (Primrec.and.comp h0 h1) h0))

private def step (values : List Bool) : Option Bool :=
  some (assemble values.length ((children values.length).map (fun i => values.getD i false)))

private theorem step_primitive : Primrec step := by
  have hs : Primrec (fun p : List Bool × Nat => p.1.getD p.2 false) :=
    (Primrec.list_getD false).comp Primrec.fst Primrec.snd
  have hm : Primrec (fun values : List Bool =>
      (children values.length).map (fun i => values.getD i false)) :=
    Primrec.list_map (children_primitive.comp Primrec.list_length) hs.to₂
  exact Primrec.option_some.comp (assemble_primitive.comp Primrec.list_length hm)

theorem test_primitive : Primrec Code.test := by
  have h : Primrec₂ (fun (_ : Unit) code => Code.test code) := by
    apply Primrec.nat_strong_rec _ (step_primitive.comp Primrec.snd).to₂
    intro _ code
    unfold step
    simp only [List.length_map, List.length_range]
    apply congrArg some
    rw [test_equation code]
    apply congrArg (assemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := children_decreasing code i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

theorem eliminate_primitive : Primrec Code.eliminate :=
  QuantifiedLinearProof.eliminate_primitive.comp SourceRowsCodeProof.translate_primitive

theorem decideClosed_primitive : Primrec Code.decideClosed :=
  Primrec.ite (Primrec.eq.comp test_primitive (Primrec.const true))
    (ClosedLinearProof.decideClosed_primitive.comp SourceRowsCodeProof.translate_primitive)
    (Primrec.const none)

theorem actualNumericPrograms : AdditiveSourceTargets.ActualNumericPrograms :=
  ⟨termTest_primitive, test_primitive, eliminate_primitive, decideClosed_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceProof
