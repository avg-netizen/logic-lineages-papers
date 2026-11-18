module
public import LogicLineages.CartierObserverCurrent.L0Targets
public import LogicLineages.OrdinalComparison.CartierLocalProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Proof
open LogicLineages.OrdinalComparison

theorem evenSelectorIdentity : Targets.EvenSelectorIdentity.{u} := by
  intro K _ _ _ f
  have hf := actualRationalSquareRootDecomposition K f
  have he : RatFunc.X * f =
      (RatFunc.X * actualRationalSquareRootDigit true f) ^ 2 +
        RatFunc.X * (actualRationalSquareRootDigit false f) ^ 2 := by
    conv_lhs => rw [hf]
    ring
  rw [he, actualDifferentialCartierCharacterization]

theorem cartierAdd (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2]
    (f g : RatFunc K) :
    actualDifferentialCartier (f + g) =
      actualDifferentialCartier f + actualDifferentialCartier g := by
  have hf := actualRationalSquareRootDecomposition K f
  have hg := actualRationalSquareRootDecomposition K g
  have he : f + g =
      (actualRationalSquareRootDigit false f + actualRationalSquareRootDigit false g) ^ 2 +
      RatFunc.X * (actualRationalSquareRootDigit true f + actualRationalSquareRootDigit true g) ^ 2 := by
    rw [CharTwo.add_sq, CharTwo.add_sq]
    conv_lhs => rw [hf, hg]
    ring
  rw [he, actualDifferentialCartierCharacterization]
  rfl

theorem evenSelectorLocalPowers : Targets.EvenSelectorLocalPowers.{u} := by
  intro K _ _ _ z b k
  let h : RatFunc K := RatFunc.X - RatFunc.C z
  have hn : h ≠ 0 := (actualDifferentialCartierLocalPowers K z b).1
  have split (m : Int) : RatFunc.X * (RatFunc.C b * h ^ m) =
      RatFunc.C b * h ^ (m + 1) + RatFunc.C (z * b) * h ^ m := by
    rw [zpow_add₀ hn, zpow_one, map_mul]
    dsimp [h]
    ring
  have hb := (actualDifferentialCartierLocalPowers K z b).2
  have hzb := (actualDifferentialCartierLocalPowers K z (z * b)).2
  constructor
  · change actualDifferentialCartier (RatFunc.X * (RatFunc.C b * h ^ (2 * k))) = _
    rw [split, cartierAdd, (hb k).2, (hzb k).1, add_zero]
  · change actualDifferentialCartier (RatFunc.X * (RatFunc.C b * h ^ (2 * k + 1))) = _
    rw [split, cartierAdd]
    have hi : (2 * k + 1) + 1 = 2 * (k + 1) := by ring
    rw [hi, (hb (k + 1)).1, (hzb k).2, zero_add]

#audit_namespace LogicLineages.CartierObserverCurrent.Proof
end LogicLineages.CartierObserverCurrent.Proof
