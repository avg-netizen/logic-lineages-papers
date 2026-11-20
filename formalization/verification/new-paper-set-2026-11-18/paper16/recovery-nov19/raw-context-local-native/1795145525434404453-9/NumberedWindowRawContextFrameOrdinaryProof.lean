import LogicLineages.PersistentMarking.NumberedWindowRawContextOrdinaryView
import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameBasics
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFrameOrdinaryProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFrameBasics NumberedWindowRawContextFocusProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticNodeProof NumberedWindowArithmeticFields
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

section
variable {S : Spine.Signature} {K : List Ty} {root : RawRoot} {fuel w : Nat}
variable (o : Option RawWitness)
variable (ih : ∀ Q R, run root fuel (encodeTerm Q) w (encodeTerm R) =
  o.any (fun witness => rawBit S K witness Q R))

theorem ordinaryBase (i : Nat) (Q R : NTerm) :
    follow root fuel (next 2 [i,w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.ordinaryBase i witness) Q R) := by
  rw [nextLiteral,NumberedWindowRawContextOrdinaryView.numeric]
  simp only [NumberedWindowRawContextOrdinaryView.symbolic]
  cases h : NumberedWindowRawContextOrdinaryView.args Q R with
  | none => simp [h]
  | some data =>
    rcases data with ⟨f,bs,g,rs⟩
    simp [h,followGuard,headEq,followFocus,argsAny,ih,guardAny,Option.any]


end
end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameOrdinaryProof
