import LogicLineages.PersistentMarking.NumberedWindowRawContextNumberedView
import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameBasics
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFrameNumberedBaseProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFrameBasics NumberedWindowRawContextFocusProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticNodeProof NumberedWindowArithmeticFields
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

section
variable {S : Spine.Signature} {K : List Ty} {root : RawRoot} {fuel w : Nat}
variable (o : Option RawWitness)
variable (ih : ∀ Q R, run root fuel (encodeTerm Q) w (encodeTerm R) =
  o.any (fun witness => rawBit S K witness Q R))

theorem numberedBase (i : Nat) (Q R : NTerm) :
    follow root fuel (next 3 [i,w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.numberedBase i witness) Q R) := by
  rw [nextLiteral,NumberedWindowRawContextNumberedView.baseNumeric]
  simp only [NumberedWindowRawContextNumberedView.baseSymbolic]
  cases h : NumberedWindowRawContextNumberedView.args Q R with
  | none => simp [h]
  | some data =>
    rcases data with ⟨⟨f,t,k,bs,es⟩,⟨g,u,l,rs,ss⟩⟩
    simp [h,followGuard,headEq,typeEq,natEq,argsEqCode,followFocus,argsAny,ih,guardAny,Option.any]


end
end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameNumberedBaseProof
