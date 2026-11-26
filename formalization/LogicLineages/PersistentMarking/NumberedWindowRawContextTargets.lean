import LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckBits

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextTargets
open NumberedWindowRawContextAlgorithm NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticRawRootCode
open NumberedWindowRawWitnessBits NumberedWindowRawWitnessRootBits
open NumberedWindowTypingBits NumberedWindowSyntax

def RootCalibration (S : Spine.Signature) (K : List Ty) (root : RawRoot) : Prop := ∀ q w r,
  root q w r = between decodeRoot (fun Q payload R => rootBit S K payload Q R) q w r

def WindowCalibration (S : Spine.Signature) (K : List Ty) (window : Window) : Prop := ∀ Γ τ q,
  window (Γ.map encodeTy) (encodeTy τ) q = (decodeTerm q).any (finiteWindowBit S K Γ τ)

def ExactFocus : Prop := ∀ i qs rs (test : NTerm → NTerm → Bool)
    (testCode : Nat → Nat → Bool),
  (∀ Q R, testCode (encodeTerm Q) (encodeTerm R) = test Q R) →
  (focus i (encodeArgs qs) (encodeArgs rs)).any (fun (q,r) => testCode q r) =
    argsAtBit test i qs rs

def ExactWitnessFuel : Prop := ∀ S K root, RootCalibration S K root →
  ∀ (fuel w : Nat) (Q R : NTerm),
    run root fuel (encodeTerm Q) w (encodeTerm R) =
      (decodeWitnessFuel fuel w).any (fun witness => rawBit S K witness Q R)

def ExactWindowStep : Prop := ∀ S K root window, RootCalibration S K root → WindowCalibration S K window →
  ∀ Γ τ q w r,
    windowStep root window (Γ.map encodeTy) (encodeTy τ) q w r =
      windowStepCodeBit S K Γ τ q w r

end LogicLineages.PersistentMarking.NumberedWindowRawContextTargets
