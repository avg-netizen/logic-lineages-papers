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
include ih

theorem numberedBase (i : Nat) (Q R : NTerm) :
    follow root fuel (next 3 [i,w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.numberedBase i witness) Q R) := by
  rw [nextLiteral,NumberedWindowRawContextNumberedView.baseNumeric]
  simp only [NumberedWindowRawContextNumberedView.baseSymbolic]
  cases NumberedWindowRawContextNumberedView.args Q R with
  | none => simp
  | some data =>
    rcases data with ⟨⟨f,t,k,bs,es⟩,⟨g,u,l,rs,ss⟩⟩
    simp only [Option.bind_some,Option.any_some,followGuard,followSome,headEq,typeEq,natEq,argsEqCode,followFocus]
    rw [← guardAny,argsAny]
    simp only [ih]


end
end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameNumberedBaseProof
