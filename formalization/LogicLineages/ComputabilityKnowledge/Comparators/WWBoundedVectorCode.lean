module

public import LogicLineages.ComputabilityKnowledge.WWBoundedVectorCode

@[expose] public section

/-! Complete computably constructed bounded-vector reduction supplier.
The MRDP hardness input is not supplied or assumed by this target. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.WWBoundedVectorCode

open PositiveExpression CircuitReduction WWBoundedVectorPadding
open LogicLineages.ComputabilityKnowledge.WWBoundedVectorCode

def ExactRawDomain : Prop :=
  ∀ (d : Nat) (a b : List Nat), (paddingCode d a b).isSome = true ↔
    ∃ u v : Expr (Fin d), a = encodeExpr (u.rename Fin.val) ∧ b = encodeExpr (v.rename Fin.val) ∧
      u.depth ≤ 2 ∧ v.depth ≤ 2

def LiteralConstruction : Prop :=
  ∀ (d : Nat) (u v : Expr (Fin d)), u.depth ≤ 2 → v.depth ≤ 2 →
    paddingCode d (encodeExpr (u.rename Fin.val)) (encodeExpr (v.rename Fin.val)) = some (sourceOutput u v)

def ActualUniformProgram : Prop :=
  Computable (fun p : Nat × List Nat × List Nat => paddingCode p.1 p.2.1 p.2.2)

def CertifiedSourceReduction : Prop :=
  ∀ (d : Nat) (u v : Expr (Fin d)), u.depth ≤ 2 → v.depth ≤ 2 →
    (∃ out : Output, paddingCode d (encodeExpr (u.rename Fin.val)) (encodeExpr (v.rename Fin.val)) = some out ∧
      out = sourceOutput u v) ∧
    CVector (left u v) ∧ CVector (weakRight u v) ∧ CVector (strictRight u v) ∧
    VectorBoundedNorm (left u v) ∧ VectorBoundedNorm (weakRight u v) ∧ VectorBoundedNorm (strictRight u v) ∧
    (VectorLE (left u v) (weakRight u v) ↔ ∀ ρ : Fin d → PosNat, v.eval ρ + 1 ≤ u.eval ρ) ∧
    (VectorLT (left u v) (strictRight u v) ↔ ∀ ρ : Fin d → PosNat, v.eval ρ + 1 ≤ u.eval ρ)

def Target : Prop := ExactRawDomain ∧ LiteralConstruction ∧ ActualUniformProgram ∧ CertifiedSourceReduction

end LogicLineages.ComputabilityKnowledge.Comparators.WWBoundedVectorCode
