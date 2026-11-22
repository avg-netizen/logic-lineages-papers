module
public import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighTargets
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighValueProof
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighStrictProof
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighEqualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
open FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

theorem exactOrientedSignedPair : ExactOrientedSignedPair := by
  intro f B selected F G hF hG ρ i j c nz k positive
  dsimp only
  rcases lt_trichotomy i j with forward | same | backward
  · have rev : ¬ j < i := not_lt_of_ge forward.le
    have ne : i ≠ j := ne_of_lt forward
    simp only [orientedPacket,if_pos forward,orientedMinimum,if_neg rev,if_neg ne,
      min_eq_left forward.le,max_eq_right forward.le]
    intro paid
    have result := exactStrictSignedPair f B selected F G hF hG ρ i j forward paid c nz k positive
    obtain ⟨ν,tied,_⟩ := result.2.2.1
    exact ⟨result.1,⟨ν,tied⟩,fun μ fit z ordered => (result.2.2.2 μ fit z ordered).2.2.2⟩
  · subst j
    simp only [orientedPacket,orientedMinimum,lt_irrefl,if_false,if_pos rfl,max_self]
    intro _
    have result := exactEqualRankSignedPair f B selected F G hF hG ρ i c nz k positive
    have tied : PreparedTableTied f i ρ (equalPacket F G c k positive).1 (fun _ => 0) := by
      intro t used
      exact False.elim (Nat.not_lt_zero t used)
    exact ⟨result.2.1,⟨_,tied⟩,fun μ _ z paid => (result.2.2 μ z paid).2.2.2⟩
  · have fwd : ¬ i < j := not_lt_of_ge backward.le
    have ne : i ≠ j := (ne_of_lt backward).symm
    simp only [orientedPacket,if_neg fwd,if_pos backward,orientedMinimum,if_neg ne,
      min_eq_right backward.le,max_eq_left backward.le]
    intro paid
    have nonzero : (-c) ≠ 0 := by omega
    have result := exactStrictSignedPair f B selected G F hG hF ρ j i backward paid (-c) nonzero k positive
    obtain ⟨ν,tied,_⟩ := result.2.2.1
    refine ⟨result.1,⟨ν,tied⟩,fun μ fit z ordered => ?_⟩
    exact ((result.2.2.2 μ fit z ordered).2.2.2).trans
      (exactReverseSignedPair f (Function.update ρ i z) F G i j c k positive)

end LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
