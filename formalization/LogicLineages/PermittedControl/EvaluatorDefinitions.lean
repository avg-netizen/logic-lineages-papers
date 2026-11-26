module
public import LogicLineages.PermittedControl.FactorialDefinitions
public import LogicLineages.OrdinalComparison.ActualDescent
public import LogicLineages.OrdinalComparison.EncodedDescentDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Literal nonfinite replacement, using the limit part and arbitrary control. -/
noncomputable def descentWith (f : Nat → Nat) (a : Ordinal.{0}) : Ordinal :=
  actualMaximumPredecessor (actualLimitPart a) (f (actualOrdinalNorm a))

/-- Actual well-founded first-finite endpoint and event count. No code search
or supplied termination oracle enters this independent semantics. -/
noncomputable def terminalWith (f : Nat → Nat) : Ordinal.{0} → Nat × Nat :=
  Ordinal.lt_wf.fix fun a rec =>
    if ha : a < epsilonZero then
      if hn : a < Ordinal.omega0 then (a.card.toNat, 0)
      else
        let result := rec (descentWith f a) (by
          have hd := actualNonfiniteDecomposition a (le_of_not_gt hn) ha
          exact (actualMaximumPredecessor_correct (actualLimitPart a) hd.2.1.bot_lt hd.1
            (f (actualOrdinalNorm a))).1.1.trans_le (Ordinal.mul_div_le a Ordinal.omega0))
        (result.1, result.2 + 1)
    else (0, 0)

/-- Finite states are absorbing in the numerical implementation. -/
def encodedStepWith (f : Nat → Nat) (n : Nat) : Nat :=
  if encodedFiniteTest n then n
  else encodedMaximumPredecessor (rawSplitCode n).unpair.1 (f (rawNormCode n))

def encodedStatesWith (f : Nat → Nat) (n k : Nat) : Nat := (encodedStepWith f)^[k] n

def terminalSearchWith (f : Nat → Nat) (n : Nat) : Part Nat :=
  Nat.rfind (fun k => Part.some (encodedFiniteTest (encodedStatesWith f n k)))

def evaluatorPartialWith (f : Nat → Nat) (n : Nat) : Part Nat :=
  if rawNormalCode n = 1 then
    (terminalSearchWith f n).map (fun k => encodedFiniteValue (encodedStatesWith f n k) + k)
  else Part.some 0

/-- The fallback does not assert termination; totality is an independent target. -/
noncomputable def evaluatorWith (f : Nat → Nat) (n : Nat) : Nat := by
  classical
  exact (evaluatorPartialWith f n).getOrElse 0

end LogicLineages.PermittedControl
