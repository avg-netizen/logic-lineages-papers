import LogicLineages.PersistentMarking.NumberedWindowArithmeticCopyTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationChecks
import LogicLineages.PersistentMarking.NumberedWindowAdmissionChecks
import LogicLineages.PersistentMarking.NumberedWindowRawContextFocusProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticCopyRankProof
open NumberedWindowCopyAlgorithm NumberedWindowArithmeticCopyTargets NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticCodecLaws NumberedWindowRawWitnessRootBits
open NumberedWindowAdmissionTargets

private theorem lookupExact (xs : Entries) (name : Nat) : lookup xs name = Spine.lookupRank xs name := by
  induction xs with
  | nil => rfl
  | cons row xs ih =>
    rcases row with ⟨x,arity⟩
    change (if name = x then _ else (lookup xs name).map _) = _
    rw [ih]
    rfl

theorem rankExact : ExactClassRank := by
  intro S f
  cases f <;> simp [rank,rankParts,encodeHead,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,
    pairRound,Spine.classRank,lookupExact]
  rename_i name arity
  cases h : Spine.lookupRank S.entries name with
  | none => rfl
  | some p => cases p; rfl

theorem compareExact : ExactRootRankComparisons := by
  intro S f g
  simp only [compareRanks,rankExact,precedesBit,equivalentBit]
  cases Spine.classRank S f <;> cases Spine.classRank S g <;> exact ⟨rfl,rfl⟩

theorem allowedExact (S K result f g small) :
    allowedTarget small S.entries (window S K).2 (encodeTy result) (encodeHead f) (encodeHead g) =
      (decide (result = g.result) && (if small then precedesBit S f g else equivalentBit S f g) &&
        NumberedWindowHeadEnumerationTargets.headBit S K g) := by
  unfold allowedTarget
  rw [NumberedWindowArithmeticAnnotationProof.head,NumberedWindowAdmissionChecks.exact_WindowConstants.2 S K g,
    NumberedWindowRawContextFocusProof.typeEq]
  cases small with
  | true => rw [(compareExact S f g).1]; rfl
  | false => rw [(compareExact S f g).2]; rfl
end LogicLineages.PersistentMarking.NumberedWindowArithmeticCopyRankProof
