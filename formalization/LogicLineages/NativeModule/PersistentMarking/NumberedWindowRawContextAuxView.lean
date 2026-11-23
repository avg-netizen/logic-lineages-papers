module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawContextFrameView

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextAuxView
open NumberedWindowSyntax NumberedWindowRawWitnessBits NumberedWindowLiteralEquality
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextFrameView
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode

abbrev Fields := Ty × Ty × NTerm × NTerm

def args : NTerm → NTerm → Option (Fields × Fields)
  | .auxApp s t q a,.auxApp u v r b => some ((s,t,q,a),(u,v,r,b))
  | _,_ => none

theorem numeric (w : Nat) (Q R : NTerm) :
    context 5 [w] (view Q) (view R) = (args Q R).bind (fun ((s,t,q,a),(u,v,r,b)) =>
      if encodeTy s == encodeTy u && encodeTy t == encodeTy v && encodeTerm a == encodeTerm b then
        some (encodeTerm q,w,encodeTerm r)
      else none) := by
  cases Q <;> cases R <;> rfl

theorem symbolic (S : Spine.Signature) (K : List Ty) (w : RawWitness) (Q R : NTerm) :
    rawBit S K (.auxFunction w) Q R = (args Q R).any (fun ((s,t,q,a),(u,v,r,b)) =>
      decide (s = u) && decide (t = v) && termEq a b && rawBit S K w q r) := by
  cases Q <;> cases R <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowRawContextAuxView
