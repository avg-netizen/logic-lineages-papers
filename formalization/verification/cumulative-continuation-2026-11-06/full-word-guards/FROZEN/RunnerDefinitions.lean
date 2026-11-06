module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector GuardChildMeasureCompletion

/-- Exact executable admission for the existing source letters. Unused fields
of shifts, Phi and V do not create additional restrictions. -/
def admittedLetter (D : Nat) (a : Letter) : Bool :=
  if a.1 ≤ 2 then true
  else ((a.1 == 3 || a.1 == 4) && decide (3 ≤ a.2.1)) && decide (a.2.1 ≤ D)

def admittedWord (D : Nat) (w : Word) : Bool := w.all (admittedLetter D)

def admitted (D : Nat) (p : WordPair) : Bool :=
  admittedWord D p.1 && admittedWord D p.2

/-- Current words in the original raw-variable order, accumulated cutoff,
and accumulated equality-branch comparison (LT=0, EQ=1, GT=2). -/
abbrev State := WordPair × Nat × Nat

def initial (p : WordPair) : State := (p,0,1)

/-- One literal selected child. A terminal state remains unchanged. The
deeper comparison resolves equality before the accumulated outer tie does. -/
def step (s : State) : State :=
  match selectWords s.1.1 s.1.2 with
  | none => s
  | some q =>
      (q.2.2,max s.2.1 (dispatchTail s.1.1 s.1.2),
        liftTie s.2.2 (dispatchTie s.1.1 s.1.2))

/-- Finite execution depends only on the original words and the fuel,
never on their eventual natural arguments or evaluated values. -/
def run (p : WordPair) (fuel : Nat) : State := (step^[fuel]) (initial p)

/-- Pay the current original words as well as every accumulated local
cutoff, including when the initial pair is already terminal. -/
def paidTail (s : State) : Nat :=
  max s.2.1 (max (wordTail s.1.1) (wordTail s.1.2))

/-- Malformed/unadmitted input stops immediately. An admitted input stops
exactly when the actual selector reaches an all-shift side. -/
def stopped (D : Nat) (p : WordPair) (fuel : Nat) : Bool :=
  (!(admitted D p)) || (selectWords (run p fuel).1.1 (run p fuel).1.2).isNone

/-- Explicit least-stopping search. Its all-input termination and ordinary
computability are separate obligations; no semantic oracle is part of step. -/
noncomputable def leastFuel (D : Nat) (p : WordPair) : Nat := by
  classical
  exact if h : ∃ fuel : Nat, stopped D p fuel = true then Nat.find h else 0

end LogicLineages.OrdinalComparison.FullWordGuardCompletion
