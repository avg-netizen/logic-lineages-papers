module
public import LogicLineages.OrdinalComparison.TrackedSourceDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.TrackedSourceInspectionCode

/-- Actual free-name occurrence test in raw original syntax. Entering ANY
lambda increments the tracked de Bruijn position; internal type levels do not
restrict traversal or change variable identity. -/
def occursCode (tracked : Nat) : Nat → Bool
  | n =>
    if n%8=0 then decide (n/8=tracked)
    else if h : n%8=5 ∨ n%8=6 then
      have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then occursCode tracked p.1 || occursCode tracked p.2
      else occursCode (tracked+1) p.2
    else false
termination_by n => n
decreasing_by all_goals assumption

/-- Exact curried-ground-result arity recognizer on the existing complete
simple-type codec. Reject every non-ground domain, rather than replacing its
level by one or discarding internal function arguments. -/
def arityCode : Nat → Option Nat
  | n => if hn : n=0 then some 0 else
      let p := (n-1).unpair
      have hr : p.2<n := by
        change (n-1).unpair.2<n
        have := Nat.unpair_right_le (n-1)
        omega
      if p.1=0 then (arityCode p.2).map Nat.succ else none
termination_by n => n
decreasing_by assumption
end LogicLineages.OrdinalComparison.Source.TrackedSourceInspectionCode
