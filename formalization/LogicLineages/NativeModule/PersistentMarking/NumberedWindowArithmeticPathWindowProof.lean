module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathDecodeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPathWitnessChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathWindowProof
open NumberedWindowRules NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticPathCode
open NumberedWindowRawWitnessBits NumberedWindowPathWitnessBits
open NumberedWindowArithmeticPathCheckTargets NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticPathDecodeProof

theorem step : ExactWindowStepOnCodes := by
  intro S K Γ τ src dst
  exact betweenExists encodeWitness decodeWitness
    NumberedWindowArithmeticRawWitnessCodeComplete.roundtrip
    (fun Q w R => finiteWindowWitnessBit S K Γ τ w Q R)
    (WindowStep S K (finiteC Γ) τ)
    (NumberedWindowRawWitnessChecks.exact_CertifiedFiniteWindowStep S K Γ τ) src dst

theorem path : ExactWindowPathOnCodes := by
  intro S K Γ τ src dst
  exact betweenExists encodeRawPath decodeRawPath
    NumberedWindowArithmeticPathCodeChecks.exact_RawPathListCodec.2.1
    (rawPathBit S K Γ τ) (WindowPath S K (finiteC Γ) τ)
    (NumberedWindowPathWitnessChecks.exact_CertifiedFiniteRawPath S K Γ τ) src dst

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathWindowProof
