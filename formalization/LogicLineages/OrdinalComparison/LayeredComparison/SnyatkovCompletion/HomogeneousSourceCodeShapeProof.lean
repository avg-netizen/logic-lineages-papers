module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
open HomogeneousSource

theorem exists_step (a tag : Nat) (ht : tag < 5) :
    Code.peelExists (5 * a + tag) = if tag = 4 then
      (a.unpair.1 :: (Code.peelExists a.unpair.2).1, (Code.peelExists a.unpair.2).2)
    else ([], 5 * a + tag) := by
  have hm : (5 * a + tag) % 5 = tag := by omega
  have hd : (5 * a + tag) / 5 = a := by omega
  rw [Code.peelExists, hm, hd]

theorem forall_outer (a tag : Nat) (ht : tag < 5) (hne : tag ≠ 2) :
    Code.peelForall (5 * a + tag) = ([], 5 * a + tag) := by
  have hm : (5 * a + tag) % 5 = tag := by omega
  have hn : ¬Code.forallTest (5 * a + tag) := by
    intro h
    exact hne (hm.symm.trans h.1)
  rw [Code.peelForall, if_neg hn]

theorem forall_middle (a tag : Nat) (ht : tag < 5) (hne : tag ≠ 4) :
    Code.peelForall (5 * (5 * a + tag) + 2) = ([], 5 * (5 * a + tag) + 2) := by
  have hd : (5 * (5 * a + tag) + 2) / 5 = 5 * a + tag := by omega
  have hm : (5 * a + tag) % 5 = tag := by omega
  have hn : ¬Code.forallTest (5 * (5 * a + tag) + 2) := by
    intro h
    have hh := h.2.1
    rw [hd, hm] at hh
    exact hne hh
  rw [Code.peelForall, if_neg hn]

theorem forall_inner (i a tag : Nat) (ht : tag < 5) :
    Code.peelForall (5 * (5 * Nat.pair i (5 * a + tag) + 4) + 2) =
      if tag = 2 then (i :: (Code.peelForall a).1, (Code.peelForall a).2)
      else ([], 5 * (5 * Nat.pair i (5 * a + tag) + 4) + 2) := by
  let code := 5 * (5 * Nat.pair i (5 * a + tag) + 4) + 2
  have hd : code / 5 = 5 * Nat.pair i (5 * a + tag) + 4 := by dsimp [code]; omega
  have he : code / 5 / 5 = Nat.pair i (5 * a + tag) := by rw [hd]; omega
  have hm : (5 * a + tag) % 5 = tag := by omega
  have htest : Code.forallTest code ↔ tag = 2 := by
    unfold Code.forallTest
    rw [he, Nat.unpair_pair, hm]
    have h0 : code % 5 = 2 := by dsimp [code]; omega
    have h1 : (code / 5) % 5 = 4 := by rw [hd]; omega
    simp [h0, h1]
  have hn : Code.forallName code = i := by simp only [Code.forallName, he, Nat.unpair_pair]
  have hc : Code.forallChild code = a := by
    simp only [Code.forallChild, he, Nat.unpair_pair]
    omega
  change Code.peelForall code = _
  rw [Code.peelForall]
  by_cases h : tag = 2
  · rw [if_pos (htest.mpr h), hn, hc, if_pos h]
  · rw [if_neg (fun he => h (htest.mp he)), if_neg h]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
