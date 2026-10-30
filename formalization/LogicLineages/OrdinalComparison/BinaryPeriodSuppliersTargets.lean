module
public import LogicLineages.OrdinalComparison.BinaryDenominatorDefinitions
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-! Genuine bounded suppliers for paper10 thm:actual-period, paper.tex599–621.
The odd modulus 2^r+1 is never assumed prime. Reciprocity uses the literal
source F2 polynomial evaluated through an explicit coefficient-field embedding
in an arbitrary field extension, not merely at the two points of F2 itself.
No residue/Cartier/tuple-period completion is asserted here. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualFermatShapeTwoOrder : Prop :=
  ∀ r : Nat, 0 < r → orderOf (2 : ZMod (2 ^ r + 1)) = 2 * r

def ActualBinarySourceReciprocity : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ m : Nat, ∀ z : K, z ≠ 0 →
    Polynomial.eval₂ (algebraMap (ZMod 2) K) z⁻¹ (actualBinarySourceDenominator m) =
      (z ^ actualBinarySourceDimension m)⁻¹ *
        Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator m)

end LogicLineages.OrdinalComparison.Targets
