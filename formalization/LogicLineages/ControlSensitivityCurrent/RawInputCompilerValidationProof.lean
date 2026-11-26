module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerStateProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source PrimitiveLowering GroundEquivalence
open PrimitiveGate (portGuard port_guard_success encodePort)

theorem boolean_guard_success (Γ : List Ty) (m : Nat) (raw : BooleanMatrix.RowCode)
    (h : booleanGuard (Γ.map SyntaxCode.typeCode) m raw = true) :
    ∃ row : InputNormalization.Node Γ m, encodeInputRow row = raw := by
  rcases raw with ⟨tag,a,b⟩
  by_cases ht : tag < 3
  · have hg : portGuard (Γ.map SyntaxCode.typeCode) a = true ∧
        portGuard (Γ.map SyntaxCode.typeCode) b = true := by
      simpa only [booleanGuard, if_pos ht, Bool.and_eq_true] using h
    obtain ⟨p,hp⟩ := port_guard_success Γ a hg.1
    obtain ⟨q,hq⟩ := port_guard_success Γ b hg.2
    have hh : tag = 0 ∨ tag = 1 ∨ tag = 2 := by omega
    rcases hh with rfl | rfl | rfl
    · exact ⟨.eq p q, by simp [encodeInputRow,hp,hq]⟩
    · exact ⟨.le p q, by simp [encodeInputRow,hp,hq]⟩
    · exact ⟨.lt p q, by simp [encodeInputRow,hp,hq]⟩
  · by_cases hneg : tag = 3
    · subst tag
      have hg : a < m ∧ b = 0 := by simpa [booleanGuard] using h
      exact ⟨.neg ⟨a,hg.1⟩, by simp [encodeInputRow,hg.2]⟩
    · have hg : (tag = 4 ∨ tag = 5) ∧ a < m ∧ b < m := by
        simpa [booleanGuard, ht, hneg] using h
      rcases hg with ⟨rfl | rfl, ha, hb⟩
      · exact ⟨.conj ⟨a,ha⟩ ⟨b,hb⟩, rfl⟩
      · exact ⟨.disj ⟨a,ha⟩ ⟨b,hb⟩, rfl⟩

theorem input_dag_guard_success (Γ : List Ty) (τ : Ty) (raw : Code)
    (h : inputDAGGuard (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode τ) raw = true) :
    ∃ d : Input Γ τ, encode ⟨Γ,τ,d⟩ = raw := by
  rw [inputDAGGuard, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hctx, htype⟩ := h
  obtain ⟨⟨Θ,σ,d⟩, he⟩ := (valid_iff raw).mp hv
  subst raw
  have hc : Θ = Γ := by
    have hh := congrArg (List.map SyntaxCode.decodeType) hctx
    simpa only [encode,decode_types] using hh
  have ht : σ = τ := RawValidator.type_code_injective htype
  cases hc
  cases ht
  exact ⟨d,rfl⟩

theorem unary_variable_success (Γ : List Ty) (i : Nat)
    (h : RawValidator.«variable» (Γ.map SyntaxCode.typeCode) 0 i = true) :
    ∃ x : Variable Γ .ground, variableIndex x = i := by
  have hv : (getVariable Γ Ty.ground i).isSome := by
    rw [← RawValidator.variable_status]
    exact h
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hv
  exact ⟨x, variable_index_sound Γ Ty.ground i x hx⟩

/-- Each accepted raw instruction has an actual typed constructor with the same payload. -/
inductive DecodedStep (Γ : List Ty) (m : Nat) : InputStep → Prop where
  | boolean (row : InputNormalization.Node Γ m) : DecodedStep Γ m (encodeInputRow row,none)
  | addition (a b : Port Γ) : DecodedStep Γ m ((6,encodePort a,encodePort b),none)
  | literal (k : Nat) : DecodedStep Γ m ((7,k,0),none)
  | observation (d : Input Γ .ground) : DecodedStep Γ m ((8,0,0),some (encode ⟨Γ,.ground,d⟩))
  | unary (h : Input [] (.arrow .ground .ground)) (x : Variable Γ .ground) :
      DecodedStep Γ m ((9,variableIndex x,0),some (encode ⟨[],.arrow .ground .ground,h⟩))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
