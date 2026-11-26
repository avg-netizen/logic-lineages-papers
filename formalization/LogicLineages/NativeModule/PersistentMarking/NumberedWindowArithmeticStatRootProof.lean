module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticStatRootTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCopyRankProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRootComparisonProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowStatChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawContextFrameView

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticStatRootProof
open NumberedWindowArithmeticStatRootTargets NumberedWindowStatRootAlgorithm NumberedWindowArithmeticCopyRankProof
open NumberedWindowArithmeticRootComparisonProof NumberedWindowArithmeticRawRootCode
open NumberedWindowRawContextFrameView NumberedWindowSyntax NumberedWindowRawWitnessRootBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks NumberedWindowAdmissionTargets
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode

private theorem parse (q : NTerm) :
    NumberedWindowFieldAlgorithm.unpackNode (encodeTerm q) = some (view q) := by
  cases q <;> exact readNode _ _

theorem statExact : ExactStatRoot := by
  intro S K part
  funext a b
  apply onCodes
  intro q r
  simp only [parse,Option.any_some]
  cases q with
  | numbered f τ k bs es =>
    cases k with
    | zero => cases r <;> rfl
    | succ k =>
      cases r <;> try rfl
      rename_i g target
      change (NumberedWindowCopyAlgorithm.allowedTarget false S.entries (window S K).2
          (encodeTy τ) (encodeHead f) (encodeHead g) &&
        NumberedWindowStatAlgorithm.replacement (encodeArgs bs) (encodeReplacement part) (encodeArgs target)) = _
      rw [allowedExact,NumberedWindowStatChecks.exact_Replacement (encodeArgs bs) (encodeReplacement part)
          (encodeArgs target),exact_ArgsCodec.2.1,exact_ArgsCodec.2.1,NumberedWindowArithmeticReplacementCodeProof.partRound]
      rfl
  | _ => rfl

theorem invalid : RejectedStatPartition := by
  intro S K part bad src dst
  have reject (q r : Nat) : NumberedWindowStatAlgorithm.replacement q part r = false := by
    rw [NumberedWindowStatChecks.exact_Replacement q part r,bad]
    cases decodeArgs q <;> rfl
  have allRows (q r) : rows S.entries (window S K).2 part q r = false := by
    simp [rows,reject]
  unfold stat NumberedWindowMarkRootAlgorithm.guarded
  cases NumberedWindowFieldAlgorithm.unpackNode src <;>
    cases NumberedWindowFieldAlgorithm.unpackNode dst <;> simp [allRows]
end LogicLineages.PersistentMarking.NumberedWindowArithmeticStatRootProof
