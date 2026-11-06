module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion
open PolynomialGraphCompletion

/-- Literal three-way outcomes: LT=0, EQ=1, GT=2. -/
def orderNat (a b : Nat) : Nat := if a < b then 0 else if a = b then 1 else 2
def orderInt (a b : Int) : Nat := if a < b then 0 else if a = b then 1 else 2

/-- A stripped head preserves strict child order and resolves its equality. -/
def liftTie (tie outcome : Nat) : Nat := if outcome = 1 then tie else outcome
def reverseOrder (outcome : Nat) : Nat :=
  if outcome = 0 then 2 else if outcome = 2 then 0 else 1
def lexOrder (first second : Nat) : Nat := liftTie second first

/-- A finite disjunction of literal signs of one word-linear row. -/
abbrev GuardFormula := List Nat
abbrev Guards := GuardFormula × GuardFormula × GuardFormula

def signFormula (tie desired : Nat) : GuardFormula :=
  [0,1,2].filter (fun sign => decide (liftTie tie sign = desired))
def makeGuards (tie : Nat) : Guards :=
  (signFormula tie 0,signFormula tie 1,signFormula tie 2)
def guardAt (guards : Guards) (desired : Nat) : GuardFormula :=
  if desired = 0 then guards.1 else if desired = 1 then guards.2.1 else guards.2.2

def SignAtom (sign : Nat) (value : Int) : Prop :=
  (sign = 0 ∧ value < 0) ∨ (sign = 1 ∧ value = 0) ∨ (sign = 2 ∧ 0 < value)
noncomputable def GuardHolds (g : GuardFormula) (r : Row) (ν : Nat → Nat) : Prop :=
  ∃ sign ∈ g, SignAtom sign (RowValue r ν)

/-- Names zero and one remain the original left and right raw variables. -/
def pairEnv (x y : Nat) (name : Nat) : Nat :=
  if name = 0 then x else if name = 1 then y else 0

/-- Every occurrence of the maximum variable is linear, and every nonempty
word is applied only to the other original variable. -/
def LinearInMaximum (r : Row) : Prop :=
  ∀ a ∈ r.2, a.2.1 ≤ 1 ∧ (a.2.1 = 0 → a.2.2 = [])

end LogicLineages.OrdinalComparison.FullWordGuardCompletion
