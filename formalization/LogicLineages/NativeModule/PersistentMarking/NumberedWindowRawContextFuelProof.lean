module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawContextDispatchProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFuelProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFrameBasics NumberedWindowRawContextDispatchProof
open NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticTermCode NumberedWindowArithmeticFields
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

private theorem runDispatched (root : RawRoot) (fuel q w r tag : Nat) (ws : List Nat)
    (h : NumberedWindowFieldAlgorithm.unpackNode w = some (tag,ws)) :
    run root (fuel+1) q w r = dispatched root fuel q r tag ws := by
  simp only [run,iterate,tick,h]
  cases tag with
  | zero => rcases ws with _ | ⟨p,_ | ⟨x,tail⟩⟩ <;> rfl
  | succ tag => rfl

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
      rcases row with ⟨p,ws⟩
      have hc : NumberedWindowFieldAlgorithm.unpackNode w = some (p,ws) := by
        rwa [← exact_ExactTaggedNodeCodec.2]
      rw [runDispatched root fuel _ _ _ p ws hc]
      simpa only [decodeWitnessFuel,hn,Option.bind_some] using exactDispatch h fuel ih p ws Q R

end LogicLineages.PersistentMarking.NumberedWindowRawContextFuelProof
