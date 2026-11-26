module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawContextFrameView

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextLamView
open NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextFrameView
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode

def args : NTerm → NTerm → Option (Ty × NTerm × Ty × NTerm)
  | .lam s q,.lam t r => some (s,q,t,r)
  | _,_ => none

theorem numeric (w : Nat) (Q R : NTerm) :
    context 1 [w] (view Q) (view R) = (args Q R).bind (fun (s,q,t,r) =>
      if encodeTy s == encodeTy t then some (encodeTerm q,w,encodeTerm r) else none) := by
  cases Q <;> cases R <;> rfl

theorem symbolic (S : Spine.Signature) (K : List Ty) (w : RawWitness) (Q R : NTerm) :
    rawBit S K (.lam w) Q R = (args Q R).any (fun (s,q,t,r) =>
      decide (s = t) && rawBit S K w q r) := by
  cases Q <;> cases R <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowRawContextLamView
