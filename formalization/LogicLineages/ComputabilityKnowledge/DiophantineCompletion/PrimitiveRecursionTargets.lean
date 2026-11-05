module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionTargets
open Dioph PrimitiveRecursion

/-- Any finite natural sequence has an actual sparse cipher; no bound on the
values is required in advance, and length zero is included. -/
def FiniteTraceCipher : Prop := ∀ len (f : Nat → Nat),
  ∃ q code : Nat, Cipher.IsCipherOf len q f code

def DigitDiophantine : Prop := ∀ (α : Type) (Q C I : (α → Nat) → Nat),
  DiophFn Q → DiophFn C → DiophFn I → DiophFn (fun v => digit (Q v) (C v) (I v))

/-- Exact ordinary primitive recursion, with every base/step computation
defined and the recursive constructor unchanged. Zero steps are included. -/
def OrdinaryPrecTraceSpecification : Prop := ∀ (base step : Nat.Partrec.Code) a n y,
  y ∈ Nat.Partrec.Code.eval (.prec base step) (Nat.pair a n) ↔
    ∃ f : Nat → Nat, partialTrace base step a n f ∧ f n = y

def CodedPrecTraceSpecification : Prop := ∀ (base step : Nat.Partrec.Code) a n y,
  y ∈ Nat.Partrec.Code.eval (.prec base step) (Nat.pair a n) ↔ codedTrace base step a n y

def CodedPrecTraceDiophantine : Prop := ∀ (base step : Nat.Partrec.Code),
  Dioph (graph (Nat.Partrec.Code.eval base)) →
  Dioph (graph (Nat.Partrec.Code.eval step)) →
  Dioph {v : Fin 3 → Nat | codedTrace base step (v 0) (v 1) (v 2)}

/-- Actual ordinary code-constructor graph closure. This is not an assumed
full-code induction theorem or a universal evaluator. -/
def OrdinaryPrecGraphClosure : Prop := ∀ (base step : Nat.Partrec.Code),
  Dioph (graph (Nat.Partrec.Code.eval base)) →
  Dioph (graph (Nat.Partrec.Code.eval step)) →
  Dioph (graph (Nat.Partrec.Code.eval (.prec base step)))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionTargets
