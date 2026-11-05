module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinear
open NormalForm SourceRows

/-- The free literal summands of the existing quantified-row syntax. Binding
removes every occurrence with that name only within its original scope. -/
def occurrences : QFormula → List Summand
  | .matrix p => LinearBlock.occurrences p
  | .negative p => occurrences p
  | .conjunction p q => occurrences p ++ occurrences q
  | .existsNat i p => (occurrences p).filter (fun s => s.name != i)

/-- Tests only free occurrences of a name, retaining ordinary binder shadowing. -/
def freeLinear (i : Nat) : QFormula → Bool
  | .matrix p => LinearRows.isLinear i p
  | .negative p => freeLinear i p
  | .conjunction p q => freeLinear i p && freeLinear i q
  | .existsNat j p => if i = j then true else freeLinear i p

/-- A decidable syntactic fragment. Every bound occurrence must be linear;
nonlinear terms at free names remain arbitrary correlated parameters. -/
def admissible : QFormula → Bool
  | .matrix _ => true
  | .negative p => admissible p
  | .conjunction p q => admissible p && admissible q
  | .existsNat i p => admissible p && freeLinear i p

/-- Concrete quantifier elimination, with correctness restricted by the exact
admissibility test above. Negation and named binders are not rearranged. -/
def eliminate : QFormula → Formula
  | .matrix p => p
  | .negative p => .negative (eliminate p)
  | .conjunction p q => .conjunction (eliminate p) (eliminate q)
  | .existsNat i p => LinearRows.eliminate i (eliminate p)

namespace Code
/-- All-code programs use the existing radix-four quantified-row encoding. -/
def freeLinear (i code : Nat) : Bool :=
  if code % 4 = 0 then LinearRows.Code.isLinear i (code / 4)
  else if code % 4 = 1 then freeLinear i (code / 4)
  else if code % 4 = 2 then
    freeLinear i (code / 4).unpair.1 && freeLinear i (code / 4).unpair.2
  else if i = (code / 4).unpair.1 then true
  else freeLinear i (code / 4).unpair.2
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega

def admissible (code : Nat) : Bool :=
  if code % 4 = 0 then true
  else if code % 4 = 1 then admissible (code / 4)
  else if code % 4 = 2 then
    admissible (code / 4).unpair.1 && admissible (code / 4).unpair.2
  else admissible (code / 4).unpair.2 &&
    freeLinear (code / 4).unpair.1 (code / 4).unpair.2
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega

def eliminate (code : Nat) : Nat :=
  if code % 4 = 0 then code / 4
  else if code % 4 = 1 then 6 * eliminate (code / 4) + 3
  else if code % 4 = 2 then
    6 * Nat.pair (eliminate (code / 4).unpair.1) (eliminate (code / 4).unpair.2) + 4
  else LinearRows.Code.eliminate (code / 4).unpair.1 (eliminate (code / 4).unpair.2)
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinear
