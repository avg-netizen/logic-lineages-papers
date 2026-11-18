module
public import LogicLineages.ControlSensitivityCurrent.RawPlanRenamingTargets
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerOperationPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanRenaming

open PlanCompiler (Instruction rename_gate_primitive)

theorem lift_table_primitive : Primrec liftTable :=
  Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_map Primrec.id (Primrec.succ.comp Primrec.snd).to₂)

theorem rename_step_primitive :
    Primrec (fun p : RenameState × Instruction => renameStep p.1 p.2) := by
  let A := RenameState × Instruction
  let B := A × (Code × Code)
  let C := A × (PrimitiveGate.GateCode ⊕ PUnit)
  let D := C × PrimitiveGate.GateCode
  let E := C × PUnit
  have hctx : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have htable : Primrec (fun p : A => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hacc : Primrec (fun p : A => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hpair (project : B → Code) (hp : Primrec project) :
      Primrec (fun p => Operations.renameCode p.1.1.1 p.1.1.2.1 (project p)) :=
    Operations.rename_code_primitive.comp
      ((hctx.comp Primrec.fst).pair ((htable.comp Primrec.fst).pair hp))
  have ha := hpair _ (Primrec.fst.comp (Primrec.snd : Primrec (fun p : B => p.2)))
  have hb := hpair _ (Primrec.snd.comp (Primrec.snd : Primrec (fun p : B => p.2)))
  have heq : Primrec (fun p : B => (.inl (Operations.renameCode p.1.1.1 p.1.1.2.1 p.2.1,
    Operations.renameCode p.1.1.1 p.1.1.2.1 p.2.2) : Instruction)) :=
    Primrec.sumInl.comp (ha.pair hb)
  have hleft := (hctx.comp Primrec.fst).pair ((htable.comp Primrec.fst).pair
    (Primrec.list_cons.comp heq (hacc.comp Primrec.fst)))
  have hd : Primrec (fun p : D => p.1.1) := Primrec.fst.comp Primrec.fst
  have hg : Primrec (fun p : D => (.inr (.inl (PlanCompiler.renameGateRaw p.1.1.1.2.1 p.2)) : Instruction)) :=
    Primrec.sumInr.comp (Primrec.sumInl.comp (rename_gate_primitive.comp ((htable.comp hd).pair Primrec.snd)))
  have hgate := (hctx.comp hd).pair ((htable.comp hd).pair (Primrec.list_cons.comp hg (hacc.comp hd)))
  have he : Primrec (fun p : E => p.1.1) := Primrec.fst.comp Primrec.fst
  have hinstr : Primrec (fun p : E => p.1.1.2) := Primrec.snd.comp he
  have hbind := (Primrec.list_cons.comp (Primrec.const 0) (hctx.comp he)).pair
    ((lift_table_primitive.comp (htable.comp he)).pair (Primrec.list_cons.comp hinstr (hacc.comp he)))
  have hright := Primrec.sumCasesOn (Primrec.snd : Primrec (fun p : C => p.2)) hgate.to₂ hbind.to₂
  apply (Primrec.sumCasesOn Primrec.snd hleft.to₂ hright.to₂).of_eq
  rintro ⟨⟨target, table, rev⟩, i⟩
  rcases i with ⟨a,b⟩ | (g | unit) <;> rfl

theorem primitive : RawPlanRenamingTargets.Primitive := by
  let A := List Nat × List Nat × List Instruction
  let B := A × (RenameState × Instruction)
  have hinit := (Primrec.fst : Primrec (fun p : A => p.1)).pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.const ([] : List Instruction)))
  have hfold := Primrec.list_foldl (Primrec.snd.comp Primrec.snd) hinit
    (rename_step_primitive.comp (Primrec.snd : Primrec (fun p : B => p.2))).to₂
  exact Primrec.list_reverse.comp (Primrec.snd.comp (Primrec.snd.comp hfold))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanRenaming
