module

public import LogicLineages.PersistentMarking.NumberedWindowMarkRootAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathCheckBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootTargets
open NumberedWindowMarkRootAlgorithm NumberedWindowArithmeticRawRootCode NumberedWindowRawWitnessRootBits
open NumberedWindowArithmeticPathCheckBits

def rootOn (S : Spine.Signature) (K : List Ty) (w : RawRootWitness) (src dst : Nat) : Bool :=
  between decodeRoot (fun q v r => rootBit S K v q r) src (encodeRoot w) dst

def ExactMarkRoot : Prop := ∀ S K k, mark k = rootOn S K (.mark k)
def ExactLowerRoot : Prop := ∀ S K, lower = rootOn S K .lower
def ExactBottomRoot : Prop := ∀ S K, bottom = rootOn S K .bottom
end LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootTargets
