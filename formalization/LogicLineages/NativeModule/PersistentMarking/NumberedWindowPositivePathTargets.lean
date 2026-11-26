module

public import LogicLineages.PersistentMarking.NumberedWindowPositivePathAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathTargets
open NumberedWindowPositivePathAlgorithm
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticAllContextBits

def Callbacks (S : Spine.Signature) (K : List Ty) (step : Step) (least : Least) : Prop :=
  (∀ Γ τ q w r, step (Γ.map encodeTy) (encodeTy τ) q w r =
    windowStepCodeBit S K Γ τ q w r) ∧
  (∀ Γ τ q, least (Γ.map encodeTy) (encodeTy τ) q =
    (decodeTerm q).bind (leastCode S K Γ τ))

def ExactPositivePath : Prop := ∀ S K step least, Callbacks S K step least →
  ∀ Γ τ source cert target,
    positive step least (Γ.map encodeTy) (encodeTy τ) source cert target =
      positiveClassPathCodeBit S K Γ τ source cert target

def ExactAddressRS : Prop := ∀ S K step least, Callbacks S K step least →
  ∀ source cert target, addressRS step least source cert target =
    addressRSBit S K source cert target

end LogicLineages.PersistentMarking.NumberedWindowPositivePathTargets
