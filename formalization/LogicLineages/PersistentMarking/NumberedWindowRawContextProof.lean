import LogicLineages.PersistentMarking.NumberedWindowRawContextFuelProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFuelProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticTermCodeChecks

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
