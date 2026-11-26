module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerNonePrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerSomePrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open PlanCompiler (Instruction)

theorem advance_primitive :
    Primrec (fun p : InputState × InputStep => advance p.1 p.2) := by
  let A := InputState × InputStep
  let B := A × Code
  have hs : Primrec (fun p : A => p.1) := Primrec.fst
  have hrow : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hf := advance_none_primitive.comp (hs.pair hrow)
  have hg := advance_some_primitive.comp ((hs.comp Primrec.fst).pair
    ((hrow.comp Primrec.fst).pair (Primrec.snd : Primrec (fun p : B => p.2))))
  apply (Primrec.option_casesOn hp hf hg.to₂).of_eq
  rintro ⟨s,row,payload⟩
  cases payload <;> rfl

theorem lower_primitive :
    Primrec (fun p : List Instruction × Lowering => lower p.1 p.2) := by
  let A := List Instruction × Lowering
  let B := A × Nat
  have ht : Primrec (fun p : A => p.1) := Primrec.fst
  have hg : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hctx : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnil := Primrec.list_append.comp hg ht
  have hsome := BinaryPlanCompiler.primitive.comp ((hctx.comp Primrec.fst).pair
    ((Primrec.snd : Primrec (fun p : B => p.2)).pair (ht.comp Primrec.fst)))
  exact Primrec.option_casesOn hn hnil hsome.to₂

theorem finish_input_primitive :
    Primrec (fun p : InputState × Nat => finishInput p.1 p.2) := by
  let A := InputState × Nat
  let B := A × (List Instruction × Lowering)
  have hs : Primrec (fun p : A => p.1) := Primrec.fst
  have hroot : Primrec (fun p : A => p.2) := Primrec.snd
  have hrows := Primrec.fst.comp (Primrec.snd.comp hs)
  have hports := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hpending := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hmatrix := BooleanMatrix.primitive.comp (hports.pair (hrows.pair hroot))
  have hstep := lower_primitive.comp (Primrec.snd : Primrec (fun p : B => p.2))
  have hout := Primrec.list_foldl hpending hmatrix hstep.to₂
  exact Primrec.ite (Primrec.nat_lt.comp hroot (Primrec.list_length.comp hrows))
    (Primrec.option_some.comp hout) (Primrec.const none)

private theorem advance_option_primitive :
    Primrec (fun p : Option InputState × InputStep => p.1.bind (fun s => advance s p.2)) := by
  let A := Option InputState × InputStep
  let B := A × InputState
  have hi : Primrec (fun p : B => p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.option_bind Primrec.fst (advance_primitive.comp (Primrec.snd.pair hi)).to₂

theorem run_from_primitive :
    Primrec (fun p : InputState × InputCode => runFrom p.1 p.2) := by
  let A := InputState × InputCode
  let B := A × (Option InputState × InputStep)
  have hs : Primrec (fun p : A => p.1) := Primrec.fst
  have hi : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hroot : Primrec (fun p : A × InputState => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hscan := Primrec.list_foldl hi (Primrec.option_some.comp hs)
    (advance_option_primitive.comp (Primrec.snd : Primrec (fun p : B => p.2))).to₂
  exact Primrec.option_bind hscan (finish_input_primitive.comp (Primrec.snd.pair hroot)).to₂

theorem effective : RawInputCompilerTargets.Effective :=
  (run_from_primitive.comp (((Primrec.fst : Primrec (fun p : List Nat × InputCode => p.1)).pair
    (Primrec.const (([],[],[]) : List BooleanMatrix.RowCode × List Nat × List Lowering))).pair Primrec.snd)).to_comp

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
