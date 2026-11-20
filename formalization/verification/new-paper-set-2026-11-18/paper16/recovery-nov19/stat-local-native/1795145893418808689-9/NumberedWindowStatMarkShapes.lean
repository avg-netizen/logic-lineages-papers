import LogicLineages.PersistentMarking.NumberedWindowStatAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameView

namespace LogicLineages.PersistentMarking.NumberedWindowStatMarkShapes
open NumberedWindowStatAlgorithm NumberedWindowRawContextFrameView
open NumberedWindowSyntax NumberedWindowPrimitiveWitnessBits NumberedWindowLiteralEquality
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTyCode
open NumberedWindowAnnotationAlgorithm (declaration)

inductive Atom where
  | ordinary (f : Head) (bs : NArgs) (g : Head) (t : Ty) (bt et : NArgs)
  | numbered (f : Head) (s : Ty) (k : Nat) (bs es : NArgs)
      (g : Head) (t : Ty) (l : Nat) (bt et : NArgs)

def atoms : NTerm → NTerm → Option Atom
  | .ordinary f bs,.numbered g t _ bt et => some (.ordinary f bs g t bt et)
  | .numbered f s k bs es,.numbered g t l bt et => some (.numbered f s k bs es g t l bt et)
  | _,_ => none

def numeric : Atom → Bool
  | .ordinary f bs g t bt et =>
    (encodeHead f == encodeHead g) &&
    (encodeTy t == (declaration (encodeHead f)).1) &&
    (encodeArgs bs == encodeArgs bt) && (encodeArgs et == 0)
  | .numbered f s k bs es g t l bt et =>
    (encodeHead f == encodeHead g) && (encodeTy s == encodeTy t) &&
    decide (l < k) && (encodeArgs bs == encodeArgs bt) && (encodeArgs es == encodeArgs et)

def symbolic : Atom → Bool
  | .ordinary f bs g t bt .nil => decide (f = g) && decide (t = f.result) && argsEq bs bt
  | .ordinary _ _ _ _ _ (.cons ..) => false
  | .numbered f s k bs es g t l bt et =>
    decide (f = g) && decide (s = t) && decide (l < k) && argsEq bs bt && argsEq es et

theorem numericShape (Q R : NTerm) :
    atomic (view Q) (view R) = (atoms Q R).any numeric := by
  cases Q <;> cases R <;> rfl

def lambdas : NTerm → NTerm → Option (Ty × NTerm × Ty × NTerm)
  | .lam s q,.lam t r => some (s,q,t,r)
  | _,_ => none

theorem numericPeel (Q R : NTerm) :
    peelParts (view Q) (view R) = (lambdas Q R).bind (fun (s,q,t,r) =>
      if encodeTy s == encodeTy t then some (encodeTerm q,encodeTerm r) else none) := by
  cases Q <;> cases R <;> rfl

theorem symbolicShape (Q R : NTerm) :
    markBit Q R = match lambdas Q R with
      | some (s,q,t,r) => decide (s = t) && markBit q r
      | none => (atoms Q R).any symbolic := by
  cases Q <;> cases R <;> try rfl
  all_goals rename_i et; cases et <;> rfl

theorem atomicOfLambda {Q R : NTerm} (z : lambdas Q R = some data) :
    atoms Q R = none := by
  cases Q <;> cases R <;> simp [lambdas,atoms] at z ⊢

theorem childCode {Q R : NTerm} {s q t r} (h : lambdas Q R = some (s,q,t,r)) :
    Q = .lam s q := by
  cases Q <;> cases R <;> simp [lambdas] at h
  obtain ⟨rfl,rfl,_,_⟩ := h
  rfl

end LogicLineages.PersistentMarking.NumberedWindowStatMarkShapes
