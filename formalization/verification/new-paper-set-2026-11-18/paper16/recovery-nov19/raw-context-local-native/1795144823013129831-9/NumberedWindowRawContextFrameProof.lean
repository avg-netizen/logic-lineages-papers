import LogicLineages.PersistentMarking.NumberedWindowRawContextFocusProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFrameProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets
open NumberedWindowRawContextFocusProof NumberedWindowSyntax NumberedWindowRawWitnessBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticNodeProof NumberedWindowArithmeticFields
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

private theorem followGuard (root : RawRoot) (fuel : Nat) (b : Bool) (frame : Option Frame) :
    follow root fuel (if b then frame else none) = (b && follow root fuel frame) := by
  cases b <;> simp

private theorem followFocus (root : RawRoot) (fuel w i : Nat) (qs rs : NArgs) :
    follow root fuel ((focus i (encodeArgs qs) (encodeArgs rs)).map (fun (q,r) => (q,w,r))) =
      argsAtBit (fun Q R => run root fuel (encodeTerm Q) w (encodeTerm R)) i qs rs := by
  have result : ∀ p : Option Pair,
      follow root fuel (p.map (fun (q,r) => (q,w,r))) =
        p.any (fun (q,r) => run root fuel q w r) := by
    rintro (_ | ⟨q,r⟩) <;> simp [Option.any]
  rw [result]
  apply exactFocus
  intro Q R
  rfl

private theorem guardAny {α} (b : Bool) (o : Option α) (p : α → Bool) :
    (b && o.any p) = o.any (fun x => b && p x) := by
  cases o <;> simp [Option.any]

@[simp] private theorem anyFalse {α} (o : Option α) :
    o.any (fun _ => false) = false := by cases o <;> rfl

private theorem showNode (tag : Nat) (xs : List Nat) :
    NumberedWindowFieldAlgorithm.unpackNode (encodeNode tag xs) = some (tag,xs) := by
  rw [← exact_ExactTaggedNodeCodec.2]
  exact nodeRound tag xs

section
variable {S : Spine.Signature} {K : List Ty} {root : RawRoot} {fuel w : Nat}
variable (o : Option RawWitness)
variable (ih : ∀ Q R, run root fuel (encodeTerm Q) w (encodeTerm R) =
  o.any (fun witness => rawBit S K witness Q R))

theorem lam (Q R : NTerm) :
    follow root fuel (next 1 [w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.lam witness) Q R) := by
  cases Q <;> cases R <;>
    simp [next,encodeTerm,showNode,context,followGuard,typeEq,ih,guardAny,rawBit]

theorem ordinaryBase (i : Nat) (Q R : NTerm) :
    follow root fuel (next 2 [i,w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.ordinaryBase i witness) Q R) := by
  cases Q <;> cases R <;>
    simp [next,encodeTerm,showNode,context,followGuard,followFocus,headEq,ih,guardAny,argsAny,rawBit]

theorem numberedBase (i : Nat) (Q R : NTerm) :
    follow root fuel (next 3 [i,w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.numberedBase i witness) Q R) := by
  cases Q <;> cases R <;>
    simp [next,encodeTerm,showNode,context,followGuard,followFocus,headEq,typeEq,natEq,
      argsEqCode,ih,guardAny,argsAny,rawBit]

theorem numberedExtra (i : Nat) (Q R : NTerm) :
    follow root fuel (next 4 [i,w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.numberedExtra i witness) Q R) := by
  cases Q <;> cases R <;>
    simp [next,encodeTerm,showNode,context,followGuard,followFocus,headEq,typeEq,natEq,
      argsEqCode,ih,guardAny,argsAny,rawBit]

theorem auxFunction (Q R : NTerm) :
    follow root fuel (next 5 [w] (encodeTerm Q) (encodeTerm R)) =
      o.any (fun witness => rawBit S K (.auxFunction witness) Q R) := by
  cases Q <;> cases R <;>
    simp [next,encodeTerm,showNode,context,followGuard,typeEq,termEqCode,ih,guardAny,rawBit]

end
end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameProof
