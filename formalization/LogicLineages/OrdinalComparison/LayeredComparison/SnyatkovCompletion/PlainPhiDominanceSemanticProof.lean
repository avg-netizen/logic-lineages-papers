module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceAlgebraProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceGrowthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof
open NormalForm PlainPhiDominance

theorem actualMaximalRawDominance : PlainPhiDominanceTargets.ActualMaximalRawDominance := by
  intro r hp i ν hthreshold hframe hactive leader hleader hmax
  have halg := exactCollectedEvaluation r hp ν
  have hsupp := CommonHeadCollectedRow.Proof.literalCollectedSupport (phiData r ν)
  have hcoef := (hsupp.2.1 leader hleader).1
  have hraw := active_below_leader i r ν hactive leader hmax
  have hlin := linearPart_bound r ν (ν i) hframe
  have hR : (linearPart r ν).natAbs ≤
      mass r * leader.2 + (mass r * shiftMass r + r.1.natAbs) := by
    have hm := Nat.mul_le_mul_left (mass r) hraw
    nlinarith
  have hn : mass r + mass r + (mass r * shiftMass r + r.1.natAbs) + 1 ≤ leader.2 := by
    unfold threshold at hthreshold
    omega
  rw [halg.1]
  exact collected_sign (CommonHeadCollectedRow.collect (phiData r ν)) hsupp.1
    (mass r) (mass r) (mass r * shiftMass r + r.1.natAbs) (linearPart r ν)
    halg.2 leader hleader hcoef hmax hR hn

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof
