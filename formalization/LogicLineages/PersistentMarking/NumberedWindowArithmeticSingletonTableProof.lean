import LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonTargets
import LogicLineages.PersistentMarking.NumberedWindowShiftTableProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonTableProof
open NumberedWindowSingletonAlgorithm
open NumberedWindowShiftAlgorithm (earlier argsNext)
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)
open NumberedWindowArithmeticPair (pair)

theorem earlierExact (inserted depth bound : Nat) {n code offset : Nat}
    (hc : code < n) (hd : offset ≤ bound) :
    earlier (table inserted depth bound n) code offset = computed inserted depth bound code offset :=
  NumberedWindowShiftTableProof.lookupOfRecurrence (table inserted depth bound)
    (fun code offset t => next inserted depth offset code t) bound rfl (fun _ => rfl) hc hd

theorem computedNode (a c b d tag : Nat) (fs : List Nat) :
    (computed a c b (encodeNode tag fs) d).1 =
      termParts (table a c b (encodeNode tag fs)) a c d tag fs := by
  simp [computed,next,← exact_ExactTaggedNodeCodec.2,nodeRound]

theorem computedCons (a c b d q r : Nat) (h : d ≤ b) :
    (computed a c b (pair q r + 1) d).2 =
      pair (computed a c b q d).1 (computed a c b r d).2 + 1 := by
  change argsNext d (pair q r + 1) _ = _
  simp [argsNext,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound,earlierExact,
    ← NumberedWindowActualPairAlgorithmChecks.currentPair,Nat.lt_succ_of_le (pairBounds q r).1,
    Nat.lt_succ_of_le (pairBounds q r).2,h]
end LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonTableProof
