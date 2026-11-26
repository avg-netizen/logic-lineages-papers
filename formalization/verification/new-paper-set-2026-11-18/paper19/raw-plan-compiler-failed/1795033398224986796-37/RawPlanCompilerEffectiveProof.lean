module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerStepPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

theorem push_context_primitive :
    Primrec (fun p : List Nat × Instruction => pushContext p.1 p.2) := by
  let A := List Nat × Instruction
  let B : Type := A × (PrimitiveGate.GateCode ⊕ PUnit)
  have hctx : Primrec (fun p : B => p.1.1) := Primrec.fst.comp Primrec.fst
  have hgate := hctx.comp (Primrec.fst : Primrec (fun p : B × PrimitiveGate.GateCode => p.1))
  have hbinder := Primrec.list_cons.comp (Primrec.const 0)
    (hctx.comp (Primrec.fst : Primrec (fun p : B × PUnit => p.1)))
  have hright := Primrec.sumCasesOn Primrec.snd hgate.to₂ hbinder.to₂
  have hleft : Primrec (fun p : A × (Code × Code) => p.1.1) := Primrec.fst.comp Primrec.fst
  apply (Primrec.sumCasesOn Primrec.snd hleft.to₂ hright.to₂).of_eq
  rintro ⟨context,i⟩
  rcases i with eqs | (g | unit) <;> rfl

theorem end_context_primitive :
    Primrec (fun p : List Nat × List Instruction => endContext p.1 p.2) :=
  Primrec.list_foldl Primrec.snd Primrec.fst
    (push_context_primitive.comp (Primrec.snd : Primrec (fun p : (List Nat × List Instruction) ×
      (List Nat × Instruction) => p.2))).to₂

theorem run_state_primitive :
    Primrec (fun p : List Nat × List Instruction => runState p.1 p.2) := by
  let A := List Nat × List Instruction
  let B := A × (Instruction × Option State)
  let C := B × State
  have hlen := Primrec.list_length.comp end_context_primitive
  have htable := Primrec.list_range.comp hlen
  have hinit := Primrec.option_some.comp
    (end_context_primitive.pair (end_context_primitive.pair (htable.pair (Primrec.const ([] : ForestCode)))))
  have hins : Primrec (fun p : C => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hstep := compile_step_primitive.comp (hins.pair Primrec.snd)
  have hbind := Primrec.option_bind (Primrec.snd.comp (Primrec.snd : Primrec (fun p : B => p.2))) hstep.to₂
  exact Primrec.list_foldr Primrec.snd hinit hbind.to₂

theorem effective : RawPlanCompilerTargets.Effective :=
  (Primrec.option_map run_state_primitive (Primrec.snd.comp Primrec.snd).to₂).to_comp

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
