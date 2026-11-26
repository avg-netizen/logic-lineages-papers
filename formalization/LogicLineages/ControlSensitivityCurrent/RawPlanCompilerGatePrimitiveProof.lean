module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerOperationPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

theorem gate_step_primitive :
    Primrec (fun p : State × PrimitiveGate.GateCode => compileStep (.inr (.inl p.2)) p.1) := by
  let A := State × PrimitiveGate.GateCode
  let B := A × ForestCode
  have hstate : Primrec (fun p : A => p.1) := Primrec.fst
  have hsource := Primrec.fst.comp hstate
  have hctx := Primrec.fst.comp (Primrec.snd.comp hstate)
  have htable := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hstate))
  have hforest := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hstate))
  have hg := PrimitiveGate.gate_guard_primitive.comp (hsource.pair Primrec.snd)
  have hgate := rename_gate_primitive.comp (htable.pair Primrec.snd)
  have hlower := checked_gate_primitive.comp (hctx.pair hgate)
  have hshift := shift_forest_primitive.comp (hctx.pair hforest)
  have hp : Primrec (fun p : B => p.1) := Primrec.fst
  have hnewctx := PrimitiveGate.block_context_primitive.comp hctx
  have hnewtable := shift_indices_primitive.comp htable
  have hnewforest := Primrec.list_append.comp Primrec.snd (hshift.comp hp)
  have hfinish := (hsource.comp hp).pair ((hnewctx.comp hp).pair ((hnewtable.comp hp).pair hnewforest))
  apply (Primrec.cond hg (Primrec.option_map hlower hfinish.to₂) (Primrec.const none)).of_eq
  rintro ⟨⟨source, context, table, fs⟩, g⟩
  cases h : PrimitiveGate.gateGuard source g with
  | false => simp [compileStep, h]
  | true =>
      cases hl : PrimitiveGate.compile context (renameGateRaw table g) <;> simp [compileStep, h, hl]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
