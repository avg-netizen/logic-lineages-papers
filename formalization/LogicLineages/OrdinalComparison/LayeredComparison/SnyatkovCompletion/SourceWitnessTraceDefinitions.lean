module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTrace

def names : SourceFormula → List Nat
  | .existsNat i p => i :: names p
  | _ => []

def residual : SourceFormula → SourceFormula
  | .existsNat _ p => residual p
  | p => p

/-- Positional updates retain duplicate names and ordinary shadowing. -/
def updateTrace (ν : Nat → Nat) : List Nat → List Nat → (Nat → Nat)
  | i :: is, n :: ns => updateTrace (Function.update ν i n) is ns
  | _, _ => ν

def realizes (ν : Nat → Nat) : SourceFormula → List Nat → Prop
  | .existsNat i p, n :: ns => realizes (Function.update ν i n) p ns
  | .existsNat _ _, [] => False
  | p, [] => p.eval ν
  | _, _ :: _ => False

/-- Each selected position is the least assignment admitting a satisfying
continuation; the suffix is chosen in the resulting current environment. -/
def leastRealization (ν : Nat → Nat) : SourceFormula → List Nat → Prop
  | .existsNat i p, n :: ns =>
      (p.eval (Function.update ν i n) ∧ ∀ m < n, ¬p.eval (Function.update ν i m)) ∧
        leastRealization (Function.update ν i n) p ns
  | .existsNat _ _, [] => False
  | p, [] => p.eval ν
  | _, _ :: _ => False

/-- Concrete trace program on every raw original source code. Only a leading
existential extends the trace. Other residual formulas retain their checked
source decision, even when they contain inner binders or Boolean structure. -/
noncomputable def solve (values : List Nat) (code : Nat) : Option (List Nat) :=
  if FiniteSearchPrograms.Code.test code then
    if code % 5 = 4 then
      (LeastSourceWitness.witness (values, (code / 5).unpair.1, (code / 5).unpair.2)).bind (fun n =>
        (solve (BoundedSourcePrograms.Code.update values (code / 5).unpair.1 n) (code / 5).unpair.2).map (fun ns => n :: ns))
    else if FiniteSearchPrograms.Code.answer values code then some [] else none
  else none
termination_by code
decreasing_by
  have hp : 0 < code := by omega
  have hd := Nat.div_lt_self hp (by decide : 1 < 5)
  have hr := Nat.unpair_right_le (code / 5)
  omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTrace
