module
public import LogicLineages.OrdinalComparison.ParametricFiniteCoefficientTargets
public import Mathlib.Order.Iterate

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient.Proof

theorem iterate_count_le (G : Nat → Nat) (hi : ∀ n : Nat, n ≤ G n)
    {c a : Nat} (hca : c ≤ a) (x : Nat) : (G^[c]) x ≤ (G^[a]) x :=
  Function.monotone_iterate_of_id_le hi hca x

theorem iterate_input_le (G : Nat → Nat) (hm : StrictMono G)
    (a : Nat) {x y : Nat} (hxy : x ≤ y) : (G^[a]) x ≤ (G^[a]) y :=
  (hm.iterate a).monotone hxy

theorem formula_same_head_lt (G : Nat → Nat) (hm : StrictMono G)
    (a : Nat) {d b : Nat} (hdb : d < b) : formula G (a, d) < formula G (a, b) := by
  have h : (G^[a]) (2*a+d) < (G^[a]) (2*a+b) := (hm.iterate a) (by omega)
  change (G^[a]) (2*a+d) + a < (G^[a]) (2*a+b) + a
  omega

theorem formula_lower_head_bound (G : Nat → Nat) (hm : StrictMono G)
    (hi : ∀ n : Nat, n ≤ G n) (a c d B : Nat)
    (hca : c ≤ a) (hbudget : 2*c+d ≤ B) :
    formula G (c, d) + 1 ≤ (G^[a]) B + a + 1 := by
  have hinput := iterate_input_le G hm c hbudget
  have hcount := iterate_count_le G hi hca B
  change (G^[c]) (2*c+d) + c + 1 ≤ (G^[a]) B + a + 1
  omega

end LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient.Proof
