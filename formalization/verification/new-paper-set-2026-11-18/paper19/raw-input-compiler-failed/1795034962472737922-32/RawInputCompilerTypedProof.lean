module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerAdvanceProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source ExistentialPlan
open PlanCompiler (encodePlan)
open InputNormalization (Dag normalize arity)

theorem run_typed_from {Γ : List Ty} {m : Nat} (q : InputNormalization.Input Γ m) :
    ∀ (d : Dag Γ m) (pending : List Lowering),
      runFrom (stateOf d pending) (encodeInput q) =
        some (pending.foldl lower (encodePlan (BooleanCompiler.lower (normalize d q)))) := by
  induction q with
  | @finish Γ m root =>
      intro d pending
      have h := BooleanMatrix.typed_exactness Γ (arity m) m d.wires d.ports root
      have rootBound : root.val < (stateOf d pending).2.1.length := by rw [rows_state_length]; exact root.isLt
      simp only [encodeInput, runFrom, List.foldl_nil, Option.bind_some, finishInput,
        if_pos rootBound, InputNormalization.normalize, BooleanCompiler.lower, stateOf, encodedPorts, h]
  | boolean row q ih =>
      intro d pending
      simp only [encodeInput, run_from_cons (advance_boolean d row pending)]
      exact ih _ pending
  | add a b q ih =>
      intro d pending
      simp only [encodeInput, run_from_cons (advance_add d a b pending), ih, List.foldl_cons, lower,
        addition_chunk_exact, InputNormalization.normalize, BooleanCompiler.lower]
  | @literal Γ m k q ih =>
      intro d pending
      have hc := BinaryPlanCompiler.constant_exactness Γ k
        (BooleanCompiler.lower (normalize (d.rename (Renaming.weaken Γ .ground)) q))
      simp only [encodeInput, run_from_cons (advance_literal d k pending), ih, List.foldl_cons, lower,
        hc, InputNormalization.normalize, BooleanCompiler.lower]
  | observation t q ih =>
      intro d pending
      simp only [encodeInput, run_from_cons (advance_observation d t pending), ih, List.foldl_cons, lower,
        equation_chunk_exact, InputNormalization.normalize, BooleanCompiler.lower]
  | unary h x q ih =>
      intro d pending
      simp only [encodeInput, run_from_cons (advance_unary d h x pending), ih, List.foldl_cons, lower,
        equation_chunk_exact, InputNormalization.normalize, BooleanCompiler.lower]

theorem typed_exactness : RawInputCompilerTargets.TypedExactness := by
  intro Γ q
  exact run_typed_from q .nil []

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
