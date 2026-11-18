module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

open LogicLineages.OrdinalComparison.Source GroundEquivalence PrimitiveLowering

theorem variable_shift_index {Γ τ} (n : Nat) (x : Variable Γ τ) :
    variableIndex (shift n x) = n + variableIndex x := by
  induction n with
  | zero => simp [shift]
  | succ n ih =>
      simp only [shift, variableIndex, ih]
      omega

theorem fresh_index {Γ : List Ty} {n : Nat} (i : Fin n) :
    variableIndex (fresh (Γ := Γ) i) = i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases rfl (fun j => ?_) i
      change variableIndex (fresh (Γ := Γ) j) + 1 = j.val + 1
      rw [ih]

theorem lift_port_code {Γ : List Ty} (a : Port Γ) :
    encodePort (liftPort a) = liftPortRaw (encodePort a) := by
  cases a with
  | zero => rfl
  | var x =>
      simp only [liftPort, encodePort, liftPortRaw, Nat.add_one_ne_zero, if_false,
        variable_shift_index]
      omega

theorem aux_code (Γ : List Ty) (i : Fin 9) :
    encodePort (aux (Γ := Γ) i) = i.val + 1 := by
  simp [aux, encodePort, fresh_index]

theorem port_vertex {Γ : List Ty} (a : Port Γ) :
    encode ⟨Γ, .ground, (Expr.port a).graph⟩ =
      portRaw (Γ.map SyntaxCode.typeCode) (encodePort a) := by
  cases a <;> simp [encode, Expr.graph, portDAG, encodeGraph, node,
    portRaw, portNode, encodePort, referenceIndex, SyntaxCode.typeCode]

theorem successor_vertex {Γ : List Ty} (a : Port Γ) :
    encode ⟨Γ, .ground, (Expr.successor a).graph⟩ =
      successorRaw (Γ.map SyntaxCode.typeCode) (encodePort a) := by
  cases a <;> simp [encode, Expr.graph, portDAG, encodeGraph, node, CheckedComposition.rawNode,
    successorRaw, portNode, encodePort, referenceIndex, SyntaxCode.typeCode]

theorem erase_vertices {Γ : List Ty} (a b : Port Γ) :
    encode ⟨Γ, .ground, (Expr.erase a b).graph⟩ =
      eraseRaw (Γ.map SyntaxCode.typeCode) (encodePort a) (encodePort b) := by
  cases a <;> cases b <;> simp [encode, Expr.graph, portDAG, encodeGraph, node,
    CheckedComposition.rawNode, eraseRaw, portNode, encodePort, referenceIndex, variableIndex,
    SyntaxCode.typeCode]

theorem identity_zero_vertices (Γ : List Ty) :
    encode ⟨Γ, .ground, (Expr.identityZero : Expr Γ).graph⟩ =
      identityZeroRaw (Γ.map SyntaxCode.typeCode) := rfl

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
