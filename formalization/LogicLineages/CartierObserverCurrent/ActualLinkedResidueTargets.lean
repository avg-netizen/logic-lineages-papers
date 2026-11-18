module
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentTargets

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.ActualLinkedResidue.Targets
open LogicLineages.OrdinalComparison

/-- Full current20 lem:residue for the actual linked inputs, with genuine
translated Laurent coefficients. The negative exponent is an integer. -/
def CompleteActualResidue : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ v : Nat, 4 ≤ v →
    let u := Phi v
    let B := Phi u
    let r := Nat.log 2 B - 1
    let q := 2 ^ r + 1
    let m := u - 2
    let delta := m * (m + 1) / 2
    let e := u - 4
    let d := B - u + 3
    ∀ z : K, IsPrimitiveRoot z q →
      (actualLinkedResidueExpansion u z).coeff (-1) =
        z ^ e / Polynomial.eval₂ (algebraMap (ZMod 2) K) z
          (actualBinarySourceDenominator (d - q)) ∧
      (actualLinkedResidueExpansion u z).coeff (-1) =
        z ^ ((e : Int) - (delta : Int)) *
          Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator m) ∧
      (actualLinkedResidueExpansion u z).coeff (-1) ≠ 0 ∧
      ∀ n : Int, n < -1 → (actualLinkedResidueExpansion u z).coeff n = 0
end LogicLineages.CartierObserverCurrent.ActualLinkedResidue.Targets
