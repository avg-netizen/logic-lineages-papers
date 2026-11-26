import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameView

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextNumberedView
open NumberedWindowSyntax NumberedWindowRawWitnessBits NumberedWindowLiteralEquality
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextFrameView
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode

abbrev Fields := Head × Ty × Nat × NArgs × NArgs

def args : NTerm → NTerm → Option (Fields × Fields)
  | .numbered f t k bs es,.numbered g u l rs ss => some ((f,t,k,bs,es),(g,u,l,rs,ss))
  | _,_ => none

theorem baseNumeric (i w : Nat) (Q R : NTerm) :
    context 3 [i,w] (view Q) (view R) =
      (args Q R).bind (fun ((f,t,k,bs,es),(g,u,l,rs,ss)) =>
        if encodeHead f == encodeHead g && encodeTy t == encodeTy u && k == l &&
            encodeArgs es == encodeArgs ss then
          (focus i (encodeArgs bs) (encodeArgs rs)).map (fun (q,r) => (q,w,r))
        else none) := by
  cases Q <;> cases R <;> rfl

theorem baseSymbolic (S : Spine.Signature) (K : List Ty) (i : Nat) (w : RawWitness) (Q R : NTerm) :
    rawBit S K (.numberedBase i w) Q R =
      (args Q R).any (fun ((f,t,k,bs,es),(g,u,l,rs,ss)) =>
        decide (f = g) && decide (t = u) && decide (k = l) && argsEq es ss &&
          argsAtBit (rawBit S K w) i bs rs) := by
  cases Q <;> cases R <;> rfl

theorem extraNumeric (i w : Nat) (Q R : NTerm) :
    context 4 [i,w] (view Q) (view R) =
      (args Q R).bind (fun ((f,t,k,bs,es),(g,u,l,rs,ss)) =>
        if encodeHead f == encodeHead g && encodeTy t == encodeTy u && k == l &&
            encodeArgs bs == encodeArgs rs then
          (focus i (encodeArgs es) (encodeArgs ss)).map (fun (q,r) => (q,w,r))
        else none) := by
  cases Q <;> cases R <;> rfl

theorem extraSymbolic (S : Spine.Signature) (K : List Ty) (i : Nat) (w : RawWitness) (Q R : NTerm) :
    rawBit S K (.numberedExtra i w) Q R =
      (args Q R).any (fun ((f,t,k,bs,es),(g,u,l,rs,ss)) =>
        decide (f = g) && decide (t = u) && decide (k = l) && argsEq bs rs &&
          argsAtBit (rawBit S K w) i es ss) := by
  cases Q <;> cases R <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowRawContextNumberedView
