module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerOperationPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

theorem equation_step_primitive :
    Primrec (fun p : State × (Code × Code) => compileStep (.inl p.2) p.1) := by
  let A := State × (Code × Code)
  let B := A × Code
  let C := B × Code
  have hstate : Primrec (fun p : A => p.1) := Primrec.fst
  have hsource := Primrec.fst.comp hstate
  have hctx := Primrec.fst.comp (Primrec.snd.comp hstate)
  have htable := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hstate))
  have hforest := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hstate))
  have ha : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hat := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hbt := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  have hg : Primrec (fun p : A => equationGuard p.1.1 p.2.1 p.2.2) :=
    ((Primrec.eq.comp (Primrec.fst.comp ha) hsource).and
    ((Primrec.eq.comp (Primrec.fst.comp hb) hsource).and
      ((Primrec.eq.comp hat (Primrec.const 0)).and (Primrec.eq.comp hbt (Primrec.const 0))))).decide
  have hleft := checked_rename_primitive.comp (hctx.pair (htable.pair ha))
  have hright := (checked_rename_primitive.comp (hctx.pair (htable.pair hb))).comp
    (Primrec.fst : Primrec (fun p : B => p.1))
  have hp : Primrec (fun p : C => p.1.1) := Primrec.fst.comp Primrec.fst
  have hout := Primrec.list_cons.comp
    ((Primrec.snd.comp (Primrec.fst : Primrec (fun p : C => p.1))).pair Primrec.snd)
    (hforest.comp hp)
  have hfinish := (hsource.comp hp).pair ((hctx.comp hp).pair ((htable.comp hp).pair hout))
  have hbody := Primrec.option_bind hleft (Primrec.option_map hright hfinish.to₂).to₂
  apply (Primrec.cond hg hbody (Primrec.const none)).of_eq
  rintro ⟨⟨source, context, table, fs⟩, a, b⟩
  cases h : equationGuard source a b with
  | false => simp [compileStep, h]
  | true =>
      cases ha' : CheckedRenaming.rename context table a <;>
        cases hb' : CheckedRenaming.rename context table b <;>
        simp [compileStep, h, ha', hb']

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
