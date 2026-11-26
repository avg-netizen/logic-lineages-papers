module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalenceTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerEffectiveProof
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanStepPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalence

open RawSourceDAG InputCompiler

private theorem context_primitive : Primrec (fun n => List.replicate n (0 : Nat)) := by
  have hs : Primrec₂ (fun (_ : Nat) (xs : List Nat) => 0 :: xs) :=
    (Primrec.list_cons.comp (Primrec.const 0) Primrec.snd).to₂
  apply (Primrec.nat_iterate Primrec.id (Primrec.const ([] : List Nat)) hs).of_eq
  intro n
  simp only [id_eq]
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', List.replicate_succ, ih]

theorem counterexample_primitive :
    Primrec (fun p : Bool × Nat × Code × Code => counterexampleCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Bool × Nat × Code × Code
  have hflag : Primrec (fun p : A => p.1) := Primrec.fst
  have hn : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hctx := context_primitive.comp hn
  have htgt := Primrec.list_cons.comp (Primrec.const 0) hctx
  have ht := BinaryPlanCompiler.prefix_table_primitive.comp ((Primrec.const 1).pair hctx)
  have hsource := Operations.rename_code_primitive.comp (htgt.pair (ht.pair hb))
  have hi₁ : Primrec (fun p : A => (((8,0,0),some p.2.2.1) : InputStep)) :=
    (Primrec.const (8,0,0)).pair (Primrec.option_some.comp ha)
  have hi₂ := (Primrec.const ((8,0,0) : BooleanMatrix.RowCode)).pair (Primrec.option_some.comp hsource)
  have hi₃ : Primrec (fun p : A => (((if p.1 then 2 else 1,1,2),none) : InputStep)) := by
    apply ((Primrec.cond hflag (Primrec.const 2) (Primrec.const 1)).pair
      (Primrec.const (1,2))).pair (Primrec.const none) |>.of_eq
    intro p
    cases p.1 <;> rfl
  exact (Primrec.list_cons.comp hi₁ (Primrec.list_cons.comp hi₂
    (Primrec.list_cons.comp hi₃ (Primrec.const ([] : List InputStep))))).pair (Primrec.const 0)

theorem effective : CurrentGroundEquivalenceTargets.Effective := by
  let A := Bool × Nat × Code × Code
  have hn : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hcompile := CurrentCompiler.effective.2.comp (hn.pair counterexample_primitive.to_comp)
  refine ⟨counterexample_primitive.to_comp,?_⟩
  apply (Computable.cond Computable.fst (Computable.fst.comp hcompile) (Computable.snd.comp hcompile)).of_eq
  intro p
  cases h : p.1 <;> simp [reduce,h]

end LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalence
