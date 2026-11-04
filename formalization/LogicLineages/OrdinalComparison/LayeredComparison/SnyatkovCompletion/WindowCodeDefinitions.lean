module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCode

/-- Actual total numeric syntax substitution. Recursive calls strictly lower
the input code, independently of the size/value of the replacement term. -/
def termSubstitute (i replacement : Nat) (code : Nat) : Nat :=
  if code % 10 = 0 then code
  else if code % 10 = 1 then if code / 10 = i then replacement else code
  else if code % 10 = 2 ∨ code % 10 = 3 then
    10 * Nat.pair (termSubstitute i replacement (code / 10).unpair.1)
      (termSubstitute i replacement (code / 10).unpair.2) + code % 10
  else if code % 10 = 4 ∨ code % 10 = 5 then
    10 * Nat.pair (code / 10).unpair.1
      (termSubstitute i replacement (code / 10).unpair.2) + code % 10
  else 10 * termSubstitute i replacement (code / 10) + code % 10
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 10 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 10)
    have hr := Nat.unpair_right_le (code / 10)
    omega

def matrixSubstitute (i replacement : Nat) (code : Nat) : Nat :=
  if code % 8 = 0 then 0
  else if code % 8 = 1 then 1
  else if code % 8 = 2 ∨ code % 8 = 3 then
    8 * Nat.pair (termSubstitute i replacement (code / 8).unpair.1)
      (termSubstitute i replacement (code / 8).unpair.2) + code % 8
  else if code % 8 = 4 then
    8 * Nat.pair (code / 8).unpair.1
      (termSubstitute i replacement (code / 8).unpair.2) + 4
  else if code % 8 = 5 then
    8 * matrixSubstitute i replacement (code / 8) + 5
  else
    8 * Nat.pair (matrixSubstitute i replacement (code / 8).unpair.1)
      (matrixSubstitute i replacement (code / 8).unpair.2) + code % 8
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 8 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 8)
    have hr := Nat.unpair_right_le (code / 8)
    omega

def add (a b : Nat) : Nat := 10 * Nat.pair a b + 2
def subtract (a b : Nat) : Nat := 10 * Nat.pair a b + 3
def numeral (n : Nat) : Nat := 10 * n
def var (i : Nat) : Nat := 10 * i + 1
def phi (a : Nat) : Nat := 10 * a + 6
def multiply (c a : Nat) : Nat := 10 * Nat.pair c a + 4
def less (a b : Nat) : Nat := 8 * Nat.pair a b + 3
def negative (p : Nat) : Nat := 8 * p + 5
def conjunction (p q : Nat) : Nat := 8 * Nat.pair p q + 6
def disjunction (p q : Nat) : Nat := 8 * Nat.pair p q + 7

def shift (a : Nat) (e : Int) : Nat :=
  subtract (add a (numeral e.toNat)) (numeral (-e).toNat)
def domain (a : Nat) (e : Int) : Nat := negative (less a (numeral (-e).toNat))
def atMost (a b : Nat) : Nat := negative (less b a)
def close (i anchor : Nat) (e : Int) (c : Nat) : Nat :=
  conjunction (domain (var i) e)
    (conjunction (atMost (phi anchor) (phi (shift (var i) e)))
      (atMost (phi (shift (var i) e)) (multiply c (phi anchor))))
def replacement (anchor : Nat) (e : Int) (d : Nat) : Nat :=
  shift (add anchor (numeral d)) (-e)
def any (codes : List Nat) : Nat := codes.foldr disjunction 1

abbrev Input := Nat × (Nat × (Int × (Nat × Nat)))

/-- Concrete total all-code finite-window compiler. Its valid-code calibration
and Computable theorem are unpaid targets, not assumptions of this definition. -/
def finiteWindow (p : Input) : Nat :=
  any ((List.range (p.2.2.2.1 + 1)).map (fun d =>
    matrixSubstitute p.1 (replacement p.2.1 p.2.2.1 d)
      (conjunction (close p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2)))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCode
