module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalForm

@[expose] public section

/-! Independent algebraic supplier for paper02 N1/N2 and lem:normalization.
All forms are actual hereditary finite maps; coefficients are exact finite
nonnegative affine vectors. Constant-free is the source's syntactic constant
coefficient condition, NOT vanishing at the zero tuple. No computability or
extensional-completeness conclusion is built into a definition or assumed.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalForm

open LogicLineages.ComputabilityKnowledge.ExponentialNormalForm

def ZeroAndConstants : Prop :=
  ∀ (d h : Nat) (ρ : Fin d → Nat),
    value h (zeroForm (d := d) h) ρ = 0 ∧
    constantCoefficient h (zeroForm (d := d) h) = 0 ∧
    WellFormed h (zeroForm (d := d) h) ∧
    ∀ n : Nat,
      value h (constantForm h n) ρ = n ∧
      constantCoefficient h (constantForm (d := d) h n) = n ∧
      WellFormed h (constantForm (d := d) h n)

def Addition : Prop :=
  ∀ (d h : Nat) (f g : Form d h) (ρ : Fin d → Nat),
    value h (addForm h f g) ρ = value h f ρ + value h g ρ ∧
    constantCoefficient h (addForm h f g) =
      constantCoefficient h f + constantCoefficient h g ∧
    (WellFormed h f → WellFormed h g → WellFormed h (addForm h f g))

def RemoveSyntacticConstant : Prop :=
  ∀ (d h : Nat) (f : Form d h),
    constantCoefficient h (removeConstant h f) = 0 ∧
    addForm h (constantForm h (constantCoefficient h f)) (removeConstant h f) = f ∧
    (WellFormed h f → WellFormed h (removeConstant h f))

def Target : Prop := ZeroAndConstants ∧ Addition ∧ RemoveSyntacticConstant

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalForm
