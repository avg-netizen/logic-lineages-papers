import LogicLineages.PersistentMarking.NumberedWindowRawContextFocusProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFrameBasics
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFocusProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticNodeProof NumberedWindowArithmeticFields
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

theorem terminal (root : RawRoot) (fuel : Nat) (b : Bool) :
    iterate root fuel (b,none) = (b,none) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

def follow (root : RawRoot) (fuel : Nat) (frame : Option Frame) : Bool :=
  (iterate root fuel (false,frame)).1

@[simp] theorem followNone (root : RawRoot) (fuel : Nat) : follow root fuel none = false := by
  simp [follow,terminal]

@[simp] theorem followSome (root : RawRoot) (fuel q w r : Nat) :
    follow root fuel (some (q,w,r)) = run root fuel q w r := rfl

theorem followGuard (root : RawRoot) (fuel : Nat) (b : Bool) (frame : Option Frame) :
    follow root fuel (if b then frame else none) = (b && follow root fuel frame) := by
  cases b <;> simp

theorem followFocus (root : RawRoot) (fuel w i : Nat) (qs rs : NArgs) :
    follow root fuel ((focus i (encodeArgs qs) (encodeArgs rs)).map (fun (q,r) => (q,w,r))) =
      argsAtBit (fun Q R => run root fuel (encodeTerm Q) w (encodeTerm R)) i qs rs := by
  have result : ∀ p : Option Pair,
      follow root fuel (p.map (fun (q,r) => (q,w,r))) =
        p.any (fun (q,r) => run root fuel q w r) := by
    rintro (_ | ⟨q,r⟩) <;> simp [Option.any]
  rw [result]
  exact exactFocus i qs rs (fun Q R => run root fuel (encodeTerm Q) w (encodeTerm R))
    (fun q r => run root fuel q w r) (fun _ _ => rfl)

theorem guardAny {α} (b : Bool) (o : Option α) (p : α → Bool) :
    (b && o.any p) = o.any (fun x => b && p x) := by
  cases o <;> simp [Option.any]

@[simp] theorem anyFalse {α} (o : Option α) :
    o.any (fun _ => false) = false := by cases o <;> rfl

theorem showNode (tag : Nat) (xs : List Nat) :
    NumberedWindowFieldAlgorithm.unpackNode (encodeNode tag xs) = some (tag,xs) := by
  rw [← exact_ExactTaggedNodeCodec.2]
  exact nodeRound tag xs

def view : NTerm → Nat × List Nat
  | .free t x => (0,[encodeTy t,x])
  | .bound t i => (1,[encodeTy t,i])
  | .lam t q => (2,[encodeTy t,encodeTerm q])
  | .bottom t => (3,[encodeTy t])
  | .ordinary f bs => (4,[encodeHead f,encodeArgs bs])
  | .numbered f t k bs es => (5,[encodeHead f,encodeTy t,k,encodeArgs bs,encodeArgs es])
  | .auxApp s t q a => (6,[encodeTy s,encodeTy t,encodeTerm q,encodeTerm a])

private theorem viewRound (q : NTerm) :
    NumberedWindowFieldAlgorithm.unpackNode (encodeTerm q) = some (view q) := by
  cases q <;> simp [view,encodeTerm,showNode]

theorem nextLiteral (tag : Nat) (ws : List Nat) (Q R : NTerm) :
    next tag ws (encodeTerm Q) (encodeTerm R) = context tag ws (view Q) (view R) := by
  simp [next,viewRound]

end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameBasics
