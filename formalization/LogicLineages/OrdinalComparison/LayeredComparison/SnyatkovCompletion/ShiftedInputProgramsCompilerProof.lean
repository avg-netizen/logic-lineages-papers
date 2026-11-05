module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsProof
open NormalForm ShiftedInputGuards ShiftedInputPrograms

private theorem subtract_primitive : Primrec₂ (fun a b : Int => a - b) := by
  simp only [sub_eq_add_neg]
  exact IntegerAlgorithms.Proof.add_primitive.comp Primrec.fst
    (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd)

theorem varData_primitive : Primrec Code.varData :=
  (Primrec.const 0).pair (Primrec.id.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))

theorem atom_primitive : Primrec ShiftedInputPrograms.Code.atom :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6)
      (Primrec.encode.comp ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))))
    (Primrec.const 2)

theorem negative_primitive : Primrec Code.negative :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 3)

theorem conjunction_primitive : Primrec₂ Code.conjunction :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 4)

theorem disjunction_primitive : Primrec₂ Code.disjunction :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 5)

theorem less_primitive : Primrec₂ Code.less := by
  let A := Input × Input
  have ha : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hf : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hitem : Primrec (fun p : A => ((1 : Int), Code.varData p.2.1)) :=
    (Primrec.const 1).pair (varData_primitive.comp hb)
  have hnegative : Primrec (fun p : A => ((-1 : Int), Code.varData p.1.1)) :=
    (Primrec.const (-1)).pair (varData_primitive.comp ha)
  have hfirst : Primrec (fun p : A => ShiftedInputPrograms.Code.atom (p.2.2 - 1, [(1, Code.varData p.2.1)])) :=
    atom_primitive.comp ((subtract_primitive.comp hf (Primrec.const 1)).pair
      (Primrec.list_cons.comp hitem (Primrec.const [])))
  have hsecond : Primrec (fun p : A => ShiftedInputPrograms.Code.atom (p.2.2 - p.1.2 - 1,
      [(1, Code.varData p.2.1), (-1, Code.varData p.1.1)])) :=
    atom_primitive.comp ((subtract_primitive.comp (subtract_primitive.comp hf he)
      (Primrec.const 1)).pair (Primrec.list_cons.comp hitem
        (Primrec.list_cons.comp hnegative (Primrec.const []))))
  exact conjunction_primitive.comp hfirst hsecond

theorem equal_primitive : Primrec₂ Code.equal := by
  have hleft : Primrec (fun p : Input × Input => Code.less p.1 p.2) := less_primitive
  have hright : Primrec (fun p : Input × Input => Code.less p.2 p.1) :=
    less_primitive.comp Primrec.snd Primrec.fst
  exact conjunction_primitive.comp (negative_primitive.comp hleft) (negative_primitive.comp hright)

theorem bound_primitive : Primrec₂ Code.bound := by
  let A := Nat × Input
  have hn : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : A => (p.1 : Int)) := IntegerAlgorithms.Proof.ofNat_primitive.comp Primrec.fst
  have hr : Primrec (fun p : A => ShiftedInputPrograms.Code.atom (p.2.2 - (p.1 : Int), [(1, Code.varData p.2.1)])) :=
    atom_primitive.comp ((subtract_primitive.comp he hc).pair
      (Primrec.list_cons.comp ((Primrec.const 1).pair (varData_primitive.comp hn)) (Primrec.const [])))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0) hr

private theorem step_primitive : Primrec (fun p : List Input × (List Nat × CommonHeadCompiler.Instruction) =>
    Code.step p.1 p.2.1 p.2.2) := by
  let A := List Input × (List Nat × CommonHeadCompiler.Instruction)
  have hstack : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hins : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have htag : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp hins
  have hleft : Primrec (fun p : A => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp hins)
  have hright : Primrec (fun p : A => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp hins)
  have ha : Primrec (fun p : A => p.1.getD p.2.2.2.1 (0, 0)) :=
    (Primrec.list_getD (0, (0 : Int))).comp Primrec.fst hleft
  have hb : Primrec (fun p : A => p.1.getD p.2.2.2.2 (0, 0)) :=
    (Primrec.list_getD (0, (0 : Int))).comp Primrec.fst hright
  have h0 : Primrec (fun p : A => p.2.1.getD 0 1) :=
    (Primrec.list_getD 1).comp hstack (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.1.getD 1 1) :=
    (Primrec.list_getD 1).comp hstack (Primrec.const 1)
  have hd1 : Primrec (fun p : A => p.2.1.drop 1) := Primrec.list_drop.comp (Primrec.const 1) hstack
  have hd2 : Primrec (fun p : A => p.2.1.drop 2) := Primrec.list_drop.comp (Primrec.const 2) hstack
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
    (Primrec.list_cons.comp (Primrec.const 1) hstack)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1))
      (Primrec.list_cons.comp (Primrec.const 0) hstack)
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2))
        (Primrec.list_cons.comp (equal_primitive.comp ha hb) hstack)
        (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3))
          (Primrec.list_cons.comp (less_primitive.comp ha hb) hstack)
          (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4))
            (Primrec.list_cons.comp (bound_primitive.comp hleft hb) hstack)
            (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5))
              (Primrec.list_cons.comp (negative_primitive.comp h0) hd1)
              (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6))
                (Primrec.list_cons.comp (conjunction_primitive.comp h1 h0) hd2)
                (Primrec.list_cons.comp (disjunction_primitive.comp h1 h0) hd2)))))))

theorem compile_primitive : Primrec₂ Code.compile := by
  let A := List Input × CommonHeadCode.Code
  have hs : Primrec (fun p : A × (List Nat × CommonHeadCompiler.Instruction) =>
      Code.step p.1.1 p.2.1 p.2.2) :=
    step_primitive.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hf : Primrec (fun p : A => p.2.foldl (Code.step p.1) []) :=
    Primrec.list_foldl Primrec.snd (Primrec.const []) hs.to₂
  exact (Primrec.list_getD 1).comp hf (Primrec.const 0)

theorem actualCompilerPrograms : ShiftedInputProgramsTargets.ActualCompilerPrograms :=
  ⟨less_primitive, equal_primitive, bound_primitive, compile_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsProof
