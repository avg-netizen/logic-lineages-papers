module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerTypedProof
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerDecodeStepProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source
open PlanCompiler (Instruction encodePlan)

private theorem scan_none (is : List InputStep) :
    is.foldl (fun state i => state.bind (fun s => advance s i)) (none : Option InputState) = none := by
  induction is with
  | nil => rfl
  | cons i is ih => simpa only [List.foldl_cons, Option.bind_none] using ih

private theorem run_from_step_success (s : InputState) (i : InputStep) (rest : InputCode)
    (out : List Instruction) (h : runFrom s (prependStep i rest) = some out) :
    ∃ t, advance s i = some t ∧ runFrom t rest = some out := by
  cases he : advance s i with
  | none =>
      simp only [runFrom, prependStep, List.foldl_cons, Option.bind_some, he, scan_none,
        Option.bind_none, reduceCtorEq] at h
  | some t =>
      exact ⟨t,rfl,(run_from_cons he rest).symm ▸ h⟩

theorem reconstruct_input_from {Γ : List Ty} {m : Nat} (d : InputNormalization.Dag Γ m)
    (pending : List Lowering) (is : List InputStep) (root : Nat) (out : List Instruction)
    (h : runFrom (stateOf d pending) (is,root) = some out) :
    ∃ q : InputNormalization.Input Γ m, encodeInput q = (is,root) := by
  induction is generalizing Γ m d pending with
  | nil =>
    have hr : root < m := by
      by_contra hn
      simp [runFrom,finishInput,rows_state_length,hn] at h
    exact ⟨.finish ⟨root,hr⟩, rfl⟩
  | cons i rest ih =>
    have hs : runFrom (stateOf d pending) (prependStep i (rest,root)) = some out := h
    obtain ⟨next,ha,htail⟩ := run_from_step_success _ _ _ _ hs
    have hd := decoded_step d pending i next ha
    cases hd with
    | boolean row =>
        rw [advance_boolean d row pending] at ha
        cases Option.some.inj ha
        obtain ⟨q,hq⟩ := ih _ pending htail
        exact ⟨.boolean row q, by simp only [encodeInput,hq,prependStep]⟩
    | addition a b =>
        rw [advance_add d a b pending] at ha
        cases Option.some.inj ha
        obtain ⟨q,hq⟩ := ih _ _ htail
        exact ⟨.add a b q, by simp only [encodeInput,hq,prependStep]⟩
    | literal k =>
        rw [advance_literal d k pending] at ha
        cases Option.some.inj ha
        obtain ⟨q,hq⟩ := ih _ _ htail
        exact ⟨.literal k q, by simp only [encodeInput,hq,prependStep]⟩
    | observation t =>
        rw [advance_observation d t pending] at ha
        cases Option.some.inj ha
        obtain ⟨q,hq⟩ := ih _ _ htail
        exact ⟨.observation t q, by simp only [encodeInput,hq,prependStep]⟩
    | unary f x =>
        rw [advance_unary d f x pending] at ha
        cases Option.some.inj ha
        obtain ⟨q,hq⟩ := ih _ _ htail
        exact ⟨.unary f x q, by simp only [encodeInput,hq,prependStep]⟩

theorem success_reconstruction : RawInputCompilerTargets.SuccessReconstruction := by
  rintro context ⟨is,root⟩ out h
  let Γ := context.map SyntaxCode.decodeType
  have hc : Γ.map SyntaxCode.typeCode = context := encode_types context
  have hs : runFrom (stateOf (.nil : InputNormalization.Dag Γ 0) []) (is,root) = some out := by
    change run (Γ.map SyntaxCode.typeCode) (is,root) = some out
    rwa [hc]
  obtain ⟨q,hq⟩ := reconstruct_input_from .nil [] is root out hs
  have he := typed_exactness Γ q
  rw [hc,hq,h] at he
  exact ⟨Γ,q,hc,hq,Option.some.inj he⟩

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
