module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawWitnessRootBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessBits
open Spine NumberedWindowSyntax NumberedWindowLiteralEquality
open NumberedWindowTypingBits (finiteWindowBit)
open NumberedWindowRawWitnessRootBits

/-- A single literal position in an ordered NArgs. Preserve each
prefix member and the entire suffix, not just their Primary classes. -/
def argsAtBit (test : NTerm → NTerm → Bool) : Nat → NArgs → NArgs → Bool
  | 0, .cons Q qs, .cons R rs => test Q R && argsEq qs rs
  | i+1, .cons Q qs, .cons R rs => termEq Q R && argsAtBit test i qs rs
  | _, _, _ => false

/-- A root rule or one of the five exact source context closures.
There is no auxiliary argument, bottom or binder-type closure. -/
inductive RawWitness where
  | root (w : RawRootWitness)
  | lam (w : RawWitness)
  | ordinaryBase (index : Nat) (w : RawWitness)
  | numberedBase (index : Nat) (w : RawWitness)
  | numberedExtra (index : Nat) (w : RawWitness)
  | auxFunction (w : RawWitness)

def rawBit (S : Signature) (K : List Ty) : RawWitness → NTerm → NTerm → Bool
  | .root w, Q, R => rootBit S K w Q R
  | .lam w, .lam σ Q, .lam ρ R => decide (σ = ρ) && rawBit S K w Q R
  | .ordinaryBase i w, .ordinary f qs, .ordinary g rs =>
    decide (f = g) && argsAtBit (fun Q R => rawBit S K w Q R) i qs rs
  | .numberedBase i w, .numbered f τ k bs es, .numbered g ρ l bt et =>
    decide (f = g) && decide (τ = ρ) && decide (k = l) && argsEq es et &&
      argsAtBit (fun Q R => rawBit S K w Q R) i bs bt
  | .numberedExtra i w, .numbered f τ k bs es, .numbered g ρ l bt et =>
    decide (f = g) && decide (τ = ρ) && decide (k = l) && argsEq bs bt &&
      argsAtBit (fun Q R => rawBit S K w Q R) i es et
  | .auxFunction w, .auxApp σ τ Q A, .auxApp ρ υ R B =>
    decide (σ = ρ) && decide (τ = υ) && termEq A B && rawBit S K w Q R
  | _, _, _ => false

/-- Check independent admission of both actual typed endpoints in the
same represented finite context, signature and type window. -/
def finiteWindowWitnessBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (w : RawWitness) (Q R : NTerm) : Bool :=
  rawBit S K w Q R && finiteWindowBit S K Γ τ Q && finiteWindowBit S K Γ τ R

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessBits
