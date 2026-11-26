module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateGuardProof
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateVertexProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

open LogicLineages.OrdinalComparison.Source GroundEquivalence PrimitiveLowering
open RawPrimitiveGateTargets (encodeForest)

theorem block_context_code (Γ : List Ty) :
    (Block Γ).map SyntaxCode.typeCode = blockContext (Γ.map SyntaxCode.typeCode) := by
  simp [blockContext, SyntaxCode.typeCode]

private def exprPairCode {Γ : List Ty} (e : Expr Γ × Expr Γ) : Code × Code :=
  (encode ⟨Γ, .ground, e.1.graph⟩, encode ⟨Γ, .ground, e.2.graph⟩)

private theorem unused_exact (Γ : List Ty) (start : Nat)
    (hs : start = 0 ∨ start = 1 ∨ start = 2) :
    (unused (Γ := Γ) start).map exprPairCode =
      unusedRaw (blockContext (Γ.map SyntaxCode.typeCode)) start := by
  have hfin : List.finRange 9 = [0,1,2,3,4,5,6,7,8] := rfl
  have hrange : List.range 9 = [0,1,2,3,4,5,6,7,8] := rfl
  rcases hs with rfl | rfl | rfl <;>
    simp [unused, hfin, unusedRaw, hrange, exprPairCode, port_vertex, block_context_code,
      aux_code, encodePort]

theorem forest_literal {Γ : List Ty} (g : Gate Γ) :
    forestRaw (Γ.map SyntaxCode.typeCode) (encodeGate g) = encodeForest (forest g) := by
  have h0 := unused_exact Γ 0 (Or.inl rfl)
  have h1 := unused_exact Γ 1 (Or.inr (Or.inl rfl))
  have h2 := unused_exact Γ 2 (Or.inr (Or.inr rfl))
  simp only [encodeForest, forest, List.map_map, Function.comp_def]
  change forestRaw (Γ.map SyntaxCode.typeCode) (encodeGate g) = (lower g).map exprPairCode
  cases g <;>
    simp [forestRaw, encodeGate, lower, addEquations, exprPairCode, h0, h1, h2, addRaw,
      port_vertex, successor_vertex, erase_vertices, identity_zero_vertices, lift_port_code,
      aux_code, encodePort, block_context_code]

theorem forest_exactness : RawPrimitiveGateTargets.ForestExactness := by
  intro Γ g
  have hg := (gate_exactness Γ _).mpr ⟨g, rfl⟩
  simp only [compile, hg, ite_true, forest_literal]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
