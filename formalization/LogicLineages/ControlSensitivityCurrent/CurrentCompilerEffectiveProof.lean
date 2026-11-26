module
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerTargets
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerEffectiveProof
public import LogicLineages.ControlSensitivityCurrent.RawPlanComparisonEffectiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCompiler

open RawSourceDAG
open InputCompiler (InputCode)

private theorem ground_context_primitive : Primrec (fun n => List.replicate n (0 : Nat)) := by
  have hs : Primrec₂ (fun (_ : Nat) (xs : List Nat) => 0 :: xs) :=
    (Primrec.list_cons.comp (Primrec.const 0) Primrec.snd).to₂
  apply (Primrec.nat_iterate Primrec.id (Primrec.const ([] : List Nat)) hs).of_eq
  intro n
  simp only [id_eq]
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', List.replicate_succ, ih]

theorem effective : CurrentCompilerTargets.Effective := by
  let A := Nat × InputCode
  have hctx : Computable (fun p : A => List.replicate p.1 0) := ground_context_primitive.to_comp.comp Computable.fst
  have hin := InputCompiler.effective.comp (hctx.pair Computable.snd)
  have hout := PlanComparison.effective.comp ((hctx.comp Computable.fst).pair Computable.snd)
  have hrun : Computable (fun p : A => run p.1 p.2) :=
    Computable.option_bind hin hout.to₂
  exact ⟨hrun, Computable.option_getD hrun (Computable.const fallback)⟩

end LogicLineages.ControlSensitivityCurrent.CurrentCompiler
