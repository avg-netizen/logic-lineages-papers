module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationBaseProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
open CommonLayerSyntax ScopedPhiPrograms

theorem table_at_variable (values : List Nat) (t : BaseTerm) (i : Nat) (hi : i ∈ t.variables) :
    BaseTermPrograms.valuation (Code.table values t.encode) i = PlainParameterDecision.valuation values i := by
  have hb : i < Code.bound t.encode := by
    rw [Code.bound, SourceTermGraphCodeProof.instructions_calibration]
    exact SourceRowsSupportProof.term_variable_lt_bound t i hi
  simp only [BaseTermPrograms.valuation, Code.table, PlainParameterDecision.valuation,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hb, Option.map_some, Option.getD_some]

theorem actualZeroDefaultEvaluation : ScopedPhiProgramsTargets.ActualZeroDefaultEvaluation := by
  intro values t
  unfold Code.value BaseTermPrograms.valueCode
  rw [CommonLayerSyntax.Proof.baseRoundtrip]
  apply BaseTermPrograms.Proof.supportStability
  exact table_at_variable values t

attribute [local irreducible] Nat.sqrt Nat.unpair BaseTermPrograms.valueCode

theorem bound_primitive : Primrec Code.bound :=
  SourceRowsCodeProof.bound_primitive.comp SourceTermGraphCodeProof.instructions_primitive

theorem table_primitive : Primrec₂ Code.table := by
  have hget : Primrec₂ (fun p : List Nat × Nat => fun i : Nat => p.1.getD i 0) :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map (Primrec.list_range.comp (bound_primitive.comp Primrec.snd)) hget

theorem value_computable : Computable₂ Code.value :=
  BalancedBoxEvaluation.Base.actualComputation.1.comp Computable.snd table_primitive.to_comp

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
