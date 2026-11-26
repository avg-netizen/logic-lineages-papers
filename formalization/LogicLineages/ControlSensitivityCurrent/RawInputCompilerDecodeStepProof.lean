module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerValidationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source PrimitiveLowering GroundEquivalence
open PrimitiveGate (portGuard port_guard_success encodePort)

theorem decoded_step {Γ : List Ty} {m : Nat} (d : InputNormalization.Dag Γ m)
    (pending : List Lowering) (i : InputStep) (next : InputState)
    (h : advance (stateOf d pending) i = some next) : DecodedStep Γ m i := by
  rcases i with ⟨⟨tag,a,b⟩,payload⟩
  let ctx := Γ.map SyntaxCode.typeCode
  have hctx : (stateOf d pending).1 = ctx := rfl
  cases payload with
  | none =>
    by_cases hb : tag < 6
    · have hg : booleanGuard ctx m (tag,a,b) = true := by
        cases he : booleanGuard ctx m (tag,a,b) with
        | false => simp [advance, hb, hctx, rows_state_length, he] at h
        | true => rfl
      obtain ⟨row, hr⟩ := boolean_guard_success Γ m (tag,a,b) hg
      rw [← hr]
      exact .boolean row
    · by_cases ha : tag = 6 ∧ portGuard ctx a ∧ portGuard ctx b
      · obtain ⟨rfl, hp, hq⟩ := ha
        obtain ⟨p, ep⟩ := port_guard_success Γ a hp
        obtain ⟨q, eq⟩ := port_guard_success Γ b hq
        rw [← ep, ← eq]
        exact .addition p q
      · by_cases hl : tag = 7 ∧ b = 0
        · obtain ⟨rfl,rfl⟩ := hl
          exact .literal a
        · simp [advance, hb, hctx, ha, hl] at h
  | some raw =>
    by_cases ho : tag = 8 ∧ a = 0 ∧ b = 0 ∧ inputDAGGuard ctx 0 raw
    · obtain ⟨rfl,rfl,rfl,hg⟩ := ho
      obtain ⟨t,ht⟩ := input_dag_guard_success Γ Ty.ground raw hg
      rw [← ht]
      exact .observation t
    · by_cases hu : tag = 9 ∧ b = 0 ∧ inputDAGGuard [] (SyntaxCode.arrowCode 0 0) raw ∧
          RawValidator.«variable» ctx 0 a
      · obtain ⟨rfl,rfl,hg,hv⟩ := hu
        obtain ⟨f,hf⟩ := input_dag_guard_success [] (.arrow .ground .ground) raw hg
        obtain ⟨x,hx⟩ := unary_variable_success Γ a hv
        rw [← hf, ← hx]
        exact .unary f x
      · simp [advance, hctx, ho, hu] at h

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
