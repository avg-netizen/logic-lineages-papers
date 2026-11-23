module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawContextFrameProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextDispatchProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFrameBasics NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowRawContextFrameOrdinaryProof (ordinaryBase)
open NumberedWindowRawContextFrameNumberedBaseProof (numberedBase)
open NumberedWindowRawContextFrameNumberedExtraProof (numberedExtra)
open NumberedWindowRawContextFrameAuxProof (auxFunction)
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticRawRootCode
open NumberedWindowArithmeticTermCodeChecks

def dispatched (root : RawRoot) (fuel q r : Nat) : Nat → List Nat → Bool
  | 0,[payload] => (iterate root fuel (root q payload r,none)).1
  | tag,ws => follow root fuel (next tag ws q r)

private theorem rootExact {S K root} (h : RootCalibration S K root) (Q R : NTerm) (payload : Nat) :
    root (encodeTerm Q) payload (encodeTerm R) =
      (decodeRoot payload).any (fun w => rawBit S K (.root w) Q R) := by
  rw [h]
  cases hp : decodeRoot payload <;>
    simp [between,exact_TermCodec.2.1,hp,rawBit,Option.any]

private theorem malformedFrame (root : RawRoot) (fuel tag : Nat) (ws : List Nat) (q r : Nat)
    (h : ∀ src dst, context tag ws src dst = none) :
    follow root fuel (next tag ws q r) = false := by
  unfold next
  cases NumberedWindowFieldAlgorithm.unpackNode q <;>
    cases NumberedWindowFieldAlgorithm.unpackNode r <;> simp [h]

theorem exactDispatch {S K root} (h : RootCalibration S K root) (fuel : Nat)
    (ih : ∀ w Q R, run root fuel (encodeTerm Q) w (encodeTerm R) =
      (decodeWitnessFuel fuel w).any (fun witness => rawBit S K witness Q R))
    (tag : Nat) (ws : List Nat) (Q R : NTerm) :
    dispatched root fuel (encodeTerm Q) (encodeTerm R) tag ws =
      (assembleWitness (decodeWitnessFuel fuel) tag ws).any (fun witness => rawBit S K witness Q R) := by
  rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
    rcases ws with _ | ⟨first,_ | ⟨child,_ | ⟨third,rest⟩⟩⟩
  all_goals simp only [dispatched,assembleWitness,Option.any_map,Option.any_none]
  all_goals first
    | exact (congrArg Prod.fst (terminal root fuel _)).trans (rootExact h Q R first)
    | exact NumberedWindowRawContextFrameLamProof.lam _ (ih first) Q R
    | exact ordinaryBase _ (ih child) first Q R
    | exact numberedBase _ (ih child) first Q R
    | exact numberedExtra _ (ih child) first Q R
    | exact auxFunction _ (ih first) Q R
    | exact malformedFrame root fuel _ _ _ _ (fun ⟨_,_⟩ ⟨_,_⟩ => rfl)

end LogicLineages.PersistentMarking.NumberedWindowRawContextDispatchProof
