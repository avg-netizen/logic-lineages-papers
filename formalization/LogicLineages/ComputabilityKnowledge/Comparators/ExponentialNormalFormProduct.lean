module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProduct

@[expose] public section

/-! Independently fixed full N2-constructor supplier for paper02 effective
normalization. Source multiplication is only by the constant 2^c at the affine
coefficient level. It is not arbitrary polynomial multiplication. Raising is
structural height padding, not a claimed extensional-equality decision.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormProduct

open LogicLineages.ComputabilityKnowledge.ExponentialNormalForm
open LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProduct

def AffineScaling : Prop :=
  ∀ (d k : Nat) (a : Affine d) (ρ : Fin d → Nat),
    affineValue (scaleAffine k a) ρ = k * affineValue a ρ

def HeightTransport : Prop :=
  ∀ (d h : Nat),
    raiseForm h (zeroForm (d := d) h) = zeroForm (h + 1) ∧
    Function.Injective (raiseForm (d := d) h) ∧
    ∀ (f : Form d h) (ρ : Fin d → Nat),
      value (h + 1) (raiseForm h f) ρ = value h f ρ ∧
      constantCoefficient (h + 1) (raiseForm h f) = constantCoefficient h f ∧
      (WellFormed h f → WellFormed (h + 1) (raiseForm h f))

def SourceExponentialProduct : Prop :=
  ∀ (d h : Nat) (f g : Form d h) (ρ : Fin d → Nat),
    value (h + 1) (exponentialProduct h f g) ρ =
      2 ^ value h f ρ * value h g ρ ∧
    (WellFormed h f → WellFormed h g →
      WellFormed (h + 1) (exponentialProduct h f g))

def Target : Prop := AffineScaling ∧ HeightTransport ∧ SourceExponentialProduct

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormProduct
