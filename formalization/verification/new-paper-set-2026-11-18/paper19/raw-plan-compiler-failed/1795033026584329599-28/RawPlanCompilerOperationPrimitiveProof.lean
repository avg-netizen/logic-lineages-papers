module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerTargets
public import LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateEffectiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

theorem checked_rename_primitive :
    Primrec (fun p : List Nat × List Nat × Code => CheckedRenaming.rename p.1 p.2.1 p.2.2) := by
  let A := List Nat × List Nat × Code
  have htarget : Primrec (fun p : A => p.1) := Primrec.fst
  have htable : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hcode : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hv := RawValidator.check_primitive.of_eq RawValidator.check_eq_valid
  have hg := Primrec.and.comp (hv.comp hcode)
    (CheckedRenaming.table_guard_primitive.comp ((Primrec.fst.comp hcode).pair (htarget.pair htable)))
  apply (Primrec.cond hg (Primrec.option_some.comp Operations.rename_code_primitive)
    (Primrec.const none)).of_eq
  intro p
  cases h : CheckedRenaming.guard p.1 p.2.1 p.2.2 <;> simp [CheckedRenaming.rename, h]

theorem checked_gate_primitive :
    Primrec (fun p : List Nat × PrimitiveGate.GateCode => PrimitiveGate.compile p.1 p.2) := by
  apply (Primrec.cond PrimitiveGate.gate_guard_primitive
    (Primrec.option_some.comp PrimitiveGate.forest_raw_primitive) (Primrec.const none)).of_eq
  intro p
  cases h : PrimitiveGate.gateGuard p.1 p.2 <;> simp [PrimitiveGate.compile, h]

theorem rename_port_primitive :
    Primrec (fun p : List Nat × Nat => renamePortRaw p.1 p.2) := by
  have hi : Primrec (fun p : List Nat × Nat => p.2 - 1) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp ((Primrec.list_getD 0).comp Primrec.fst hi) (Primrec.const 1))

theorem rename_gate_primitive :
    Primrec (fun p : List Nat × PrimitiveGate.GateCode => renameGateRaw p.1 p.2) := by
  let A := List Nat × PrimitiveGate.GateCode
  have htag : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : A => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hc : Primrec (fun p : A => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hd : Primrec (fun p : A => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have rename (f : A → Nat) (hf : Primrec f) : Primrec (fun p => renamePortRaw p.1 (f p)) :=
    rename_port_primitive.comp (Primrec.fst.pair hf)
  exact htag.pair ((rename _ ha).pair ((rename _ hb).pair ((rename _ hc).pair (rename _ hd))))

theorem shift_indices_primitive : Primrec (fun xs : List Nat => xs.map (fun i => i + 9)) :=
  Primrec.list_map Primrec.id (Primrec.nat_add.comp Primrec.snd (Primrec.const 9)).to₂

theorem shift_table_primitive : Primrec shiftTable :=
  shift_indices_primitive.comp (Primrec.list_range.comp Primrec.list_length)

theorem shift_forest_primitive :
    Primrec (fun p : List Nat × ForestCode => shiftForest p.1 p.2) := by
  let A := List Nat × ForestCode
  let B := A × (Code × Code)
  have hctx : Primrec (fun p : B => p.1.1) := Primrec.fst.comp Primrec.fst
  have htarget := PrimitiveGate.block_context_primitive.comp hctx
  have htable := shift_table_primitive.comp hctx
  have ha : Primrec (fun p : B => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : B => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_map Primrec.snd
    ((Operations.rename_code_primitive.comp (htarget.pair (htable.pair ha))).pair
      (Operations.rename_code_primitive.comp (htarget.pair (htable.pair hb)))).to₂

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
