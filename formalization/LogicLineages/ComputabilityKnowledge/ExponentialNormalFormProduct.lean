module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalForm

@[expose] public section

/-! Literal height transport and the normal-form (N2) exponential-product
constructor. The finite-map sum merges equal resulting exponent keys. These
definitions use no normalization, correctness or key-injectivity premise.
Their semantic/algebraic laws are separate proof obligations.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProduct

open ExponentialNormalForm

noncomputable section

def scaleAffine {d : Nat} (k : Nat) (a : Affine d) : Affine d :=
  fun i => k * a i

def raiseForm {d : Nat} : (h : Nat) → Form d h → Form d (h + 1)
  | 0, f => Finsupp.single (zeroForm 0) f
  | h + 1, f => f.sum (fun key coeff => Finsupp.single (raiseForm h key) coeff)

def exponentialProduct {d : Nat} (h : Nat) (f g : Form d h) : Form d (h + 1) :=
  match h with
  | 0 => Finsupp.single (removeConstant 0 f)
      (scaleAffine (2 ^ constantCoefficient 0 f) g)
  | h + 1 => g.sum (fun key coeff =>
      Finsupp.single (addForm (h + 1) (removeConstant (h + 1) f) (raiseForm h key))
        (scaleAffine (2 ^ constantCoefficient (h + 1) f) coeff))

end

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProduct
