module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Actual finite-map hereditary normal forms from paper02 (N1).
Height zero is an affine coefficient at the implicit zero key. At successor
height, keys are lower-height forms and coefficients are affine vectors.
WellFormed requires every nonzero-support key to be a constant-free normal
form. These are mathematical semantics; an effective finite-code refinement
and the full normalization procedure remain separate obligations.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalForm

noncomputable section

abbrev Affine (d : Nat) := Fin (d + 1) → Nat

abbrev Form (d : Nat) : Nat → Type
  | 0 => Affine d
  | h + 1 => Form d h →₀ Affine d

def affineValue {d : Nat} (a : Affine d) (ρ : Fin d → Nat) : Nat :=
  a 0 + ∑ i : Fin d, a i.succ * ρ i

def affineConstant {d : Nat} (n : Nat) : Affine d :=
  Fin.cases n (fun _ => 0)

def affineRemoveConstant {d : Nat} (a : Affine d) : Affine d :=
  Fin.cases 0 (fun i => a i.succ)

def zeroForm {d : Nat} : (h : Nat) → Form d h
  | 0 => 0
  | _ + 1 => 0

def addForm {d : Nat} : (h : Nat) → Form d h → Form d h → Form d h
  | 0, f, g => f + g
  | _ + 1, f, g => f + g

def constantForm {d : Nat} (h : Nat) (n : Nat) : Form d h :=
  match h with
  | 0 => affineConstant n
  | h + 1 => Finsupp.single (zeroForm h) (affineConstant n)

def constantCoefficient {d : Nat} : (h : Nat) → Form d h → Nat
  | 0, f => f 0
  | h + 1, f => f (zeroForm h) 0

def removeConstant {d : Nat} : (h : Nat) → Form d h → Form d h
  | 0, f => affineRemoveConstant f
  | h + 1, f => f.update (zeroForm h) (affineRemoveConstant (f (zeroForm h)))

def value {d : Nat} : (h : Nat) → Form d h → (Fin d → Nat) → Nat
  | 0, f, ρ => affineValue f ρ
  | h + 1, f, ρ => f.sum (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ)

def WellFormed {d : Nat} : (h : Nat) → Form d h → Prop
  | 0, _ => True
  | h + 1, f => ∀ key ∈ f.support,
      WellFormed h key ∧ constantCoefficient h key = 0

end

end LogicLineages.ComputabilityKnowledge.ExponentialNormalForm
