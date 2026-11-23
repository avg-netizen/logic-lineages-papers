module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRootDispatchPayloadProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRootDispatchProof
open NumberedWindowRootDispatchAlgorithm NumberedWindowRootDispatchTargets
open NumberedWindowRootDispatchPayloadProof
open NumberedWindowArithmeticMarkRootTargets NumberedWindowArithmeticRawRootCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticFieldAlgorithmChecks

private theorem partsExact {S K rules} (h : RuleCalibration S K rules) (q r tag : Nat)
    (xs : List Nat) :
    parts rules q r tag xs = (assembleRoot tag xs).any (fun w => rootOn S K w q r) := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
    rcases xs with _ | ⟨k,_ | ⟨i,_ | ⟨dom,_ | ⟨extra,tail⟩⟩⟩⟩
  all_goals first
    | rfl
    | exact selectExact h q r k i dom
    | exact statExact h q r k
    | simp [parts,assembleRoot,h.mark,h.lower,h.copy,h.fabs,h.beta,h.bottom,Option.any]

theorem rootExact : ExactRootDispatch := by
  intro S K rules h q cert r
  unfold check
  rw [← exact_ExactTaggedNodeCodec.2,betweenDecoded]
  unfold decodeRoot
  cases decodeNode cert with
  | none => rfl
  | some node =>
    rcases node with ⟨tag,xs⟩
    exact partsExact h q r tag xs

end LogicLineages.PersistentMarking.NumberedWindowRootDispatchProof
