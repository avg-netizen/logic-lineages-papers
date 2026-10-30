module
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentDefinitions
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-! Full original source paper10 lem:residue, paper.tex546–571. Residues are
actual coefficients of the translated Laurent expansion, and simple poles
are certified by a nonzero coefficient at−1 and zero coefficients below−1.
The second displayed exponent is an integer difference, not Nat subtraction.
The original input u=Phi(v),v>=4 is explicitly included, rather than assumed. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualLinkedResidueAt {K : Type u} [Field K] [Algebra (ZMod 2) K]
    (u : Nat) (z : K) : Prop :=
  (actualLinkedResidueExpansion u z).coeff (-1) =
    z ^ actualLinkedOffset u /
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z
        (actualBinarySourceDenominator (actualLinkedCutoff u - actualLinkedModulus u)) ∧
  (actualLinkedResidueExpansion u z).coeff (-1) =
    z ^ ((actualLinkedOffset u : Int) - (actualLinkedDegree u : Int)) *
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z
        (actualBinarySourceDenominator (actualLinkedTail u)) ∧
  (actualLinkedResidueExpansion u z).coeff (-1) ≠ 0 ∧
  ∀ n : Int, n < -1 → (actualLinkedResidueExpansion u z).coeff n = 0

def ActualLinkedResidueFormula : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ u : Nat, 5 ≤ u →
    ∀ z : K, IsPrimitiveRoot z (actualLinkedModulus u) → ActualLinkedResidueAt u z

def FullActualSourceResidue : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ v : Nat, 4 ≤ v →
    ∀ z : K, IsPrimitiveRoot z (actualLinkedModulus (Phi v)) → ActualLinkedResidueAt (Phi v) z

end LogicLineages.OrdinalComparison.Targets
