module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerEquationPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerGatePrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerPrimcodable
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

theorem binder_step_primitive :
    Primrec (fun s : State => compileStep (.inr (.inr PUnit.unit)) s) := by
  let A := State × (Nat × List Nat)
  have hhead : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have htail : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hresult : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hctx := Primrec.fst.comp hresult
  have htable := Primrec.list_tail.comp (Primrec.fst.comp (Primrec.snd.comp hresult))
  have hfs := Primrec.snd.comp (Primrec.snd.comp hresult)
  have hfinish := Primrec.option_some.comp (htail.pair (hctx.pair (htable.pair hfs)))
  have hcons := Primrec.ite (Primrec.eq.comp hhead (Primrec.const 0)) hfinish (Primrec.const none)
  apply (Primrec.list_casesOn Primrec.fst (Primrec.const none) hcons.to₂).of_eq
  rintro ⟨source, context, table, fs⟩
  cases source with
  | nil => rfl
  | cons n xs => cases n <;> rfl

theorem compile_step_primitive :
    Primrec (fun p : Instruction × State => compileStep p.1 p.2) := by
  let A := Instruction × State
  let B : Type := A × (PrimitiveGate.GateCode ⊕ PUnit)
  let C := B × PrimitiveGate.GateCode
  let D : Type := B × PUnit
  have hgate : Primrec (fun p : C => compileStep (.inr (.inl p.2)) p.1.1.2) :=
    gate_step_primitive.comp ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)
  have hbinder : Primrec (fun p : D => compileStep (.inr (.inr PUnit.unit)) p.1.1.2) :=
    binder_step_primitive.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hright := Primrec.sumCasesOn (Primrec.snd : Primrec (fun p : B => p.2)) hgate.to₂ hbinder.to₂
  have hleft := equation_step_primitive.comp
    ((Primrec.snd.comp (Primrec.fst : Primrec (fun p : A × (Code × Code) => p.1))).pair Primrec.snd)
  apply (Primrec.sumCasesOn Primrec.fst hleft.to₂ hright.to₂).of_eq
  rintro ⟨i,s⟩
  rcases i with p | (g | unit)
  · rfl
  · rfl
  · cases unit
    rfl

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
