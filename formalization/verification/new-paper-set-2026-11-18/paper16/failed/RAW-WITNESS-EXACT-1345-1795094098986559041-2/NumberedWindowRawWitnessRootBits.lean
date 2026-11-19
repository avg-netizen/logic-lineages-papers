import LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessBits
import LogicLineages.PersistentMarking.NumberedWindowTypingBits

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootBits
open Spine NumberedWindowSyntax NumberedWindowLiteralEquality
open NumberedWindowPrimitiveWitnessBits
open NumberedWindowHeadEnumerationTargets (headBit)

/-- Compare actual declared class ranks. Two absent ranks are never
equal as admitted classes. -/
def precedesBit (S : Signature) (f g : Head) : Bool :=
  match classRank S f, classRank S g with
  | some m, some n => decide (n < m)
  | _, _ => false

def equivalentBit (S : Signature) (f g : Head) : Bool :=
  match classRank S f, classRank S g with
  | some m, some n => decide (m = n)
  | _, _ => false

/-- All eight genuine root rules. Select supplies the actual original
base/extra side, index, and full arrow-prefix tuple. Stat supplies
the actual kept/removed/added occurrence partition. -/
inductive RawRootWitness where
  | mark (label : Nat)
  | lower
  | select (extra : Bool) (index : Nat) (domains : List Ty)
  | copy
  | stat (part : ReplacementWitness)
  | fabs
  | beta
  | bottom

def resultBit (result : Option NTerm) (R : NTerm) : Bool :=
  match result with
  | some Q => termEq Q R
  | none => false

def rootBit (S : Signature) (K : List Ty) : RawRootWitness → NTerm → NTerm → Bool
  | .mark k, .ordinary f bs, R =>
    termEq (.numbered f f.result k bs .nil) R
  | .lower, .numbered f τ (.succ k) bs es, R =>
    termEq (.numbered f τ k bs es) R
  | .select extra i domains, .numbered f τ (.succ k) bs es, R =>
    match (if extra then es else bs).get i with
    | none => false
    | some selected =>
      decide (selected.type = ArrowPrefix domains τ) &&
        resultBit (applications selected (ownerCopies f k bs es domains)) R
  | .copy, .numbered f τ (.succ k) bs es, .ordinary g target =>
    decide (τ = g.result) && precedesBit S f g && headBit S K g &&
      argsEq (ownerCopies f k bs es g.arguments) target
  | .stat part, .numbered f τ (.succ _) bs _, .ordinary g target =>
    decide (τ = g.result) && equivalentBit S f g && headBit S K g &&
      replacementBit bs target part
  | .fabs, .numbered f (.arrow σ τ) (.succ k) bs es, R =>
    termEq (.lam σ (openNumbered f σ τ k bs es)) R
  | .beta, .auxApp σ _ (.lam ρ body) a, R =>
    decide (σ = ρ) && termEq (substitute (.cons a .nil) 0 body) R
  | .bottom, Q, R => !termEq Q (.bottom Q.type) && termEq (.bottom Q.type) R
  | _, _, _ => false

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootBits
