import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFrameProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticRawRootCode
open NumberedWindowArithmeticTermCodeChecks NumberedWindowArithmeticFields
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

private theorem rootExact {S K root} (h : RootCalibration S K root) (Q R : NTerm) (payload : Nat) :
    root (encodeTerm Q) payload (encodeTerm R) =
      (decodeRoot payload).any (fun w => rawBit S K (.root w) Q R) := by
  rw [h]
  cases hp : decodeRoot payload <;>
    simp [between,exact_TermCodec.2.1,hp,rawBit,Option.any]

theorem fuelExact : ExactWitnessFuel := by
  intro S K root h fuel
  induction fuel with
  | zero => intro w Q R; rfl
  | succ fuel ih =>
    intro w Q R
    cases hn : decodeNode w with
    | none =>
      have hc : NumberedWindowFieldAlgorithm.unpackNode w = none := by
        rwa [← exact_ExactTaggedNodeCodec.2]
      simp [run,iterate,tick,hc,decodeWitnessFuel,hn,terminal]
    | some row =>
      rcases row with ⟨tag,ws⟩
      have hc : NumberedWindowFieldAlgorithm.unpackNode w = some (tag,ws) := by
        rwa [← exact_ExactTaggedNodeCodec.2]
      simp only [run,iterate,tick,hc,decodeWitnessFuel,hn,Option.bind_eq_bind,Option.bind_some]
      rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
        rcases ws with _ | ⟨first,_ | ⟨child,_ | ⟨third,rest⟩⟩⟩
      all_goals simp only [assembleWitness,Option.any_map]
      all_goals first
        | exact (congrArg Prod.fst (terminal root fuel _)).trans (rootExact h Q R first)
        | exact NumberedWindowRawContextFrameProof.lam _ (ih first) Q R
        | exact ordinaryBase _ (ih child) first Q R
        | exact numberedBase _ (ih child) first Q R
        | exact numberedExtra _ (ih child) first Q R
        | exact auxFunction _ (ih first) Q R
        | (change follow root fuel (next _ _ _ _) = false
           unfold next
           cases NumberedWindowFieldAlgorithm.unpackNode (encodeTerm Q) <;>
             cases NumberedWindowFieldAlgorithm.unpackNode (encodeTerm R) <;> simp [context])

theorem windowStepExact : ExactWindowStep := by
  intro S K root window rootEq windowEq Γ τ q w r
  unfold windowStep raw windowStepCodeBit between
  rw [NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards q,
    NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards r,windowEq,windowEq]
  simp only [NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow]
  cases hq : decodeTerm q with
  | none => simp [hq]
  | some Q =>
    cases hr : decodeTerm r with
    | none => simp [hq,hr]
    | some R =>
      have eqQ := (exact_TermCodec.1 q Q).mp hq
      have eqR := (exact_TermCodec.1 r R).mp hr
      have runEq := fuelExact S K root rootEq w w Q R
      rw [eqQ,eqR] at runEq
      change run root w q w r =
        (decodeWitness w).any (fun witness => rawBit S K witness Q R) at runEq
      rw [runEq]
      cases hw : decodeWitness w <;> simp [hq,hr,hw,Option.any,finiteWindowWitnessBit]

end LogicLineages.PersistentMarking.NumberedWindowRawContextProof
