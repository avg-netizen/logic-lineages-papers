import LogicLineages.PersistentMarking.NumberedWindowRawContextLamView
import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameBasics
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFrameLamProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFrameBasics NumberedWindowRawContextFocusProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticNodeProof NumberedWindowArithmeticFields
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

section
variable {S : Spine.Signature} {K : List Ty} {root : RawRoot} {fuel w : Nat}
variable (o : Option RawWitness)
variable (ih : ∀ Q R, run root fuel (encodeTerm Q) w (encodeTerm R) =
  o.any (fun witness => rawBit S K witness Q R))
include ih

theorem lam (Q R : NTerm) :
    follow root fuel (next 1 [w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.lam witness) Q R) := by
  rw [nextLiteral,NumberedWindowRawContextLamView.numeric]
  simp only [NumberedWindowRawContextLamView.symbolic]
  cases NumberedWindowRawContextLamView.args Q R with
  | none => simp
  | some data =>
    rcases data with ⟨s,q,t,r⟩
    simp only [Option.bind_some,followGuard,followSome,typeEq,ih,guardAny]


end
end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameLamProof
