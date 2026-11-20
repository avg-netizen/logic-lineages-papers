import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameView

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextOrdinaryView
open NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextFrameView
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticHeadCode

def args : NTerm → NTerm → Option (Head × NArgs × Head × NArgs)
  | .ordinary f bs,.ordinary g rs => some (f,bs,g,rs)
  | _,_ => none

theorem numeric (i w : Nat) (Q R : NTerm) :
    context 2 [i,w] (view Q) (view R) = (args Q R).bind (fun (f,bs,g,rs) =>
      if encodeHead f == encodeHead g then
        (focus i (encodeArgs bs) (encodeArgs rs)).map (fun (q,r) => (q,w,r))
      else none) := by
  cases Q <;> cases R <;> rfl

theorem symbolic (S : Spine.Signature) (K : List Ty) (i : Nat) (w : RawWitness) (Q R : NTerm) :
    rawBit S K (.ordinaryBase i w) Q R = (args Q R).any (fun (f,bs,g,rs) =>
      decide (f = g) && argsAtBit (rawBit S K w) i bs rs) := by
  cases Q <;> cases R <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowRawContextOrdinaryView
