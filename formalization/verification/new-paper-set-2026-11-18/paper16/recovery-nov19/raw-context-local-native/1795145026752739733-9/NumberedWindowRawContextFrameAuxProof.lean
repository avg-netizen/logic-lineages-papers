import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameBasics
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFrameAuxProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFrameBasics NumberedWindowRawContextFocusProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticNodeProof NumberedWindowArithmeticFields
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

section
variable {S : Spine.Signature} {K : List Ty} {root : RawRoot} {fuel w : Nat}
variable (o : Option RawWitness)
variable (ih : ∀ Q R, run root fuel (encodeTerm Q) w (encodeTerm R) =
  o.any (fun witness => rawBit S K witness Q R))

theorem auxFunction (Q R : NTerm) :
    follow root fuel (next 5 [w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.auxFunction witness) Q R) := by
  cases Q <;> cases R <;>
    simp [next,encodeTerm,showNode,context,followGuard,typeEq,termEqCode,ih,guardAny,rawBit]

end
end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameAuxProof
