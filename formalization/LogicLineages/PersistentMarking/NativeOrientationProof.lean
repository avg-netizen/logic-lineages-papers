import LogicLineages.PersistentMarking.NativeBetaProof
import LogicLineages.PersistentMarking.NativeCaseProof
import LogicLineages.PersistentMarking.NativeRSProof
namespace LogicLineages.PersistentMarking.NativeOrientationProof
open Spine NativeReduction

theorem primitiveOrientation : NativeOrientationTargets.PrimitiveOrientation := by
  intro S s t h
  cases h with
  | beta hb hv ho hB hoB => exact NativeBetaProof.beta S _ _ _ _ hb hv ho hB hoB
  | caseZero hA hoA hB hoB => exact NativeCaseProof.caseZero S _ _ _ hA hoA hB hoB
  | caseSucc hn hon hA hoA hB hoB => exact NativeCaseProof.caseSucc S _ _ _ _ hn hon hA hoA hB hoB
  | recZero hA hoA hB hoB => exact NativeCaseProof.recZero S _ _ _ hA hoA hB hoB
  | recSucc hn hon hA hoA hB hoB => exact NativeRSProof.recSucc S _ _ _ _ hn hon hA hoA hB hoB

theorem fullOrientation : NativeOrientationTargets.FullOrientation := by
  intro S s t h
  induction h with
  | primitive hp => exact primitiveOrientation S _ _ hp
  | context hc hs ht hr ih => exact StablePairProof.strictContext S _ _ _ _ _ hc hs ht ih
  | substitution hm hr ih => exact StablePairProof.strictSubstitution S _ _ _ ih hm
end LogicLineages.PersistentMarking.NativeOrientationProof
