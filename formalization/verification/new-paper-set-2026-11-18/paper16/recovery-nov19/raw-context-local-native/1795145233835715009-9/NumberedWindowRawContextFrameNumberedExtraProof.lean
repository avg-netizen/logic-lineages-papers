import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameBasics
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFrameNumberedExtraProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFrameBasics NumberedWindowRawContextFocusProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticNodeProof NumberedWindowArithmeticFields
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

section
variable {S : Spine.Signature} {K : List Ty} {root : RawRoot} {fuel w : Nat}
variable (o : Option RawWitness)
variable (ih : ∀ Q R, run root fuel (encodeTerm Q) w (encodeTerm R) =
  o.any (fun witness => rawBit S K witness Q R))

theorem numberedExtra (i : Nat) (Q R : NTerm) :
    follow root fuel (next 4 [i,w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.numberedExtra i witness) Q R) := by
  rw [nextLiteral]
  cases Q
  case numbered =>
    cases R
    case numbered =>
      simp [view,context,followGuard,followFocus,headEq,typeEq,natEq,
          argsEqCode,ih,guardAny,argsAny,rawBit]
    all_goals
      change follow root fuel none = _
      rw [followNone]
      cases o <;> rfl
  all_goals
    refine (congrArg (follow root fuel) (show _ = none from ?_)).trans ?_
    · cases view R <;> rfl
    · rw [followNone]
      cases o <;> cases R <;> rfl


end
end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameNumberedExtraProof
