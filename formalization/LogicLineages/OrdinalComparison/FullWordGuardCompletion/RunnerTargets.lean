module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerTargets
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector GuardChildMeasureCompletion

/-- The executable check accepts exactly the two original word grammars,
without a hidden strengthening of the finite-degree or signed-index domain. -/
def AdmissionCorrect : Prop := ∀ D p,
  admitted D p = true ↔ WordAllowed D p.1 ∧ WordAllowed D p.2

def RunEquations : Prop := ∀ p,
  run p 0 = initial p ∧ ∀ n, run p (n+1) = step (run p n)

/-- Both the local-cutoff accumulator and the full current-word payment
increase along the actual finite execution, including terminal stuttering. -/
def RunBounds : Prop :=
  (∀ s : State, s.2.1 ≤ (step s).2.1 ∧ paidTail s ≤ paidTail (step s)) ∧
  ∀ p m n, m ≤ n →
    (run p m).2.1 ≤ (run p n).2.1 ∧ paidTail (run p m) ≤ paidTail (run p n)

/-- The final accumulated cutoff pays every earlier selected local case.
This quantifies over the literal runner trace, not a proposed call graph. -/
def DispatchCoverage : Prop := ∀ p m n q, m < n →
  selectWords (run p m).1.1 (run p m).1.2 = some q →
  dispatchTail (run p m).1.1 (run p m).1.2 ≤ (run p n).2.1

def RunAdmission : Prop := ∀ D p, admitted D p = true →
  ∀ n, admitted D (run p n).1 = true

def RunTieBound : Prop := ∀ p n, (run p n).2.2 ≤ 2

/-- Every original and generated word in the finite selected trace has its
actual successive domains on the computed full payment. -/
def TraceDomains : Prop := ∀ D p, admitted D p = true → ∀ n x y,
  paidTail (run p n) ≤ x → paidTail (run p n) ≤ y →
  ∀ k, k ≤ n → WordDomain (run p k).1.1 x ∧ WordDomain (run p k).1.2 y

/-- All processed heads are represented by the accumulated equality tie.
The raw left/right inputs remain shared throughout. At fuel zero this is
the exact identity, so no unpaid domain is asserted at that stage. -/
def AccumulatedComparison : Prop := ∀ D p, admitted D p = true → ∀ n x y,
  (run p n).2.1 ≤ x → (run p n).2.1 ≤ y →
  orderNat (wordValue p.1 x) (wordValue p.2 y) =
    liftTie (run p n).2.2
      (orderNat (wordValue (run p n).1.1 x) (wordValue (run p n).1.2 y))

/-- Existing histogram well-foundedness must be applied to the actual
selected descendants. Invalid raw input stops at zero by the stated check. -/
def RunnerTerminates : Prop := ∀ D p, ∃ n : Nat, stopped D p n = true

def TerminalStability : Prop := ∀ p n,
  selectWords (run p n).1.1 (run p n).1.2 = none →
  ∀ k, run p (n+k) = run p n

/-- The actual least-search output stops, is minimal, is zero for invalid
input, and yields the same terminal state at every later admitted fuel. -/
def LeastFuelCorrect : Prop := ∀ D p,
  stopped D p (leastFuel D p) = true ∧
  (∀ n, n < leastFuel D p → stopped D p n = false) ∧
  (admitted D p = false → leastFuel D p = 0) ∧
  (admitted D p = true →
    selectWords (run p (leastFuel D p)).1.1 (run p (leastFuel D p)).1.2 = none ∧
    ∀ n, leastFuel D p ≤ n → run p n = run p (leastFuel D p))

/-- These programs compute finite syntax and cutoffs before any raw-value
comparison. Their total malformed behavior is part of the defined program. -/
def RunnerPrograms : Prop :=
  Primrec (fun p : Nat × WordPair => admitted p.1 p.2) ∧
  Primrec initial ∧ Primrec step ∧
  Primrec (fun p : WordPair × Nat => run p.1 p.2) ∧ Primrec paidTail ∧
  Primrec (fun p : Nat × WordPair × Nat => stopped p.1 p.2.1 p.2.2)

def LeastFuelProgram : Prop :=
  Computable (fun p : Nat × WordPair => leastFuel p.1 p.2)

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerTargets
