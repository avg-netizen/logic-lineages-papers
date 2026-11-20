import LogicLineages.PersistentMarking.NumberedWindowRootDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowStatChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRootDispatchPayloadProof
open NumberedWindowRootDispatchAlgorithm NumberedWindowRootDispatchTargets
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticMarkRootTargets
open NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticRawRootCode NumberedWindowArithmeticBinderCode
open NumberedWindowArithmeticRawWitnessCodeChecks

private theorem flag : flagView = decodeFlag := by
  funext n
  rcases n with _ | _ | n <;> rfl

theorem selectExact {S K rules} (h : RuleCalibration S K rules) (q r flagCode i dom : Nat) :
    parts rules q r 2 [flagCode,i,dom] =
      (assembleRoot 2 [flagCode,i,dom]).any (fun w => rootOn S K w q r) := by
  simp only [parts,flag,NumberedWindowArithmeticAddressAlgorithmChecks.exact_ExactBinderView dom,
    assembleRoot]
  cases hf : decodeFlag flagCode with
  | none => rfl
  | some extra =>
    cases hd : decodeBinders dom with
    | none => simp [hd,Option.any]
    | some Γ =>
      simpa [hd,Option.any] using congrFun (congrFun (h.select extra i Γ) q) r

theorem statExact {S K rules} (h : RuleCalibration S K rules) (q r cert : Nat) :
    parts rules q r 4 [cert] =
      (assembleRoot 4 [cert]).any (fun w => rootOn S K w q r) := by
  simp only [parts,NumberedWindowStatChecks.exact_PartitionView cert,assembleRoot]
  cases hp : decodeReplacement cert with
  | none => simp
  | some part =>
    have he := (exact_ReplacementWitnessCodec.1 cert part).mp hp
    simpa [he,Option.any] using congrFun (congrFun (h.stat part) q) r

theorem betweenDecoded (S : Spine.Signature) (K : List Ty) (q cert r : Nat) :
    between decodeRoot (fun Q w R => NumberedWindowRawWitnessRootBits.rootBit S K w Q R) q cert r =
      (decodeRoot cert).any (fun w => rootOn S K w q r) := by
  cases hw : decodeRoot cert with
  | none => cases decodeTerm q <;> cases decodeTerm r <;> simp [between,hw]
  | some witness =>
    unfold rootOn between
    rw [exact_RawRootWitnessCodec.2.1 witness] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowRootDispatchPayloadProof
