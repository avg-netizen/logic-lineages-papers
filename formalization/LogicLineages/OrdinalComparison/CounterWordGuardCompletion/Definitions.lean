module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion

/-- n represents rank n+3. Evaluation order is descending rank, ending at 3.
Only source X symbols are emitted, never companion functions or fresh inputs. -/
def leaderWord : Nat → Nat → Word
  | 0, c => [kernelLetter 3 (c+3) 0]
  | n+1, c => kernelLetter (n+4) (c+n+4) 0 :: leaderWord n c

/-- Pays every original-schedule bridge and every generated word domain. -/
def leaderTail (n c : Nat) : Nat := c+2*(n+3)+1+wordTail (leaderWord n c)

/-- Scalar comparison, the explicit source-process bridge c+rank+1,
and the generated leader word are all paid before either input is used. -/
def scalarTail (n c e : Nat) (j k : Int) : Nat :=
  max (CounterFixedShiftComparison.threshold n c e (j.natAbs+k.natAbs))
    (max (c+(n+3)+1) (leaderTail n c))

def guardTail (A B : Word) (n m c e : Nat) (j k : Int) : Nat :=
  max (reachTail A (scalarTail n c e j k))
    (reachTail B (scalarTail m e c k j))

/-- Leader preimage first, rank second, and outer signed shift only at a tie. -/
def CounterLexLT (n m : Nat) (j k : Int) (u v : Nat) : Prop :=
  u < v ∨ u = v ∧ (n < m ∨ n = m ∧ j < k)

def counterNodes (w : Word) : Nat := (w.filter (fun a => a.1 == 4)).length

end LogicLineages.OrdinalComparison.CounterWordGuardCompletion
