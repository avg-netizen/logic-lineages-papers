module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateTargets
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorLookupProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source PrimitiveLowering

theorem port_guard_typed {Γ : List Ty} (p : Port Γ) :
    portGuard (Γ.map SyntaxCode.typeCode) (encodePort p) = true := by
  cases p with
  | zero => rfl
  | var x =>
      have h := RawValidator.variable_status Γ Ty.ground (variableIndex x)
      rw [variable_roundtrip] at h
      simpa [encodePort, portGuard, SyntaxCode.typeCode] using h

theorem port_guard_success (Γ : List Ty) (p : Nat)
    (h : portGuard (Γ.map SyntaxCode.typeCode) p = true) :
    ∃ t : Port Γ, encodePort t = p := by
  cases p with
  | zero => exact ⟨.zero, rfl⟩
  | succ i =>
      have hv : (getVariable Γ Ty.ground i).isSome := by
        have hr : RawValidator.«variable» (Γ.map SyntaxCode.typeCode) 0 i = true := by
          simpa [portGuard] using h
        rw [← RawValidator.variable_status]
        exact hr
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hv
      exact ⟨.var x, by simp [encodePort, variable_index_sound Γ Ty.ground i x hx]⟩

theorem gate_exactness : RawPrimitiveGateTargets.GateExactness := by
  intro Γ raw
  constructor
  · rcases raw with ⟨tag, a, b, c, d⟩
    intro h
    simp only [gateGuard, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨ha,hb⟩,hc⟩,hd⟩,htags⟩ := h
    obtain ⟨a', ra⟩ := port_guard_success Γ a ha
    rcases htags with ((⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl⟩) | rfl) | ⟨rfl,rfl,rfl,rfl⟩
    · obtain ⟨b', rb⟩ := port_guard_success Γ b hb
      exact ⟨.eq a' b', by rw [encodeGate, ra, rb]⟩
    · obtain ⟨b', rb⟩ := port_guard_success Γ b hb
      obtain ⟨c', rc⟩ := port_guard_success Γ c hc
      exact ⟨.add a' b' c', by rw [encodeGate, ra, rb, rc]⟩
    · obtain ⟨b', rb⟩ := port_guard_success Γ b hb
      obtain ⟨c', rc⟩ := port_guard_success Γ c hc
      obtain ⟨d', rd⟩ := port_guard_success Γ d hd
      exact ⟨.sort a' b' c' d', by rw [encodeGate, ra, rb, rc, rd]⟩
    · exact ⟨.one a', by rw [encodeGate, ra]⟩
  · rintro ⟨g,rfl⟩
    have hz : portGuard (Γ.map SyntaxCode.typeCode) 0 = true := rfl
    cases g <;> simp [encodeGate, gateGuard, port_guard_typed, hz]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
