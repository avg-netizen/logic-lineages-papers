module
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Literal generated source word, exact dynamic domains, and its identification
with the already checked counter leader preimage. -/
def LeaderWordCorrect : Prop := ∀ D n c t : Nat, n+3 ≤ D → leaderTail n c ≤ t →
  WordAllowed D (leaderWord n c) ∧ WordDomain (leaderWord n c) t ∧
  wordValue (leaderWord n c) t = CounterLeaderExpansion.leaderPreimage n c t

/-- The actual source counts, not a replacement semantic convention. Every
bridge hypothesis is included in the explicit scalar cutoff. -/
def SourceShiftedCounterOrder : Prop := ∀ n m c e t u : Nat, ∀ j k : Int,
  scalarTail n c e j k ≤ t → scalarTail m e c k j ≤ u →
  0 < (sourceCount (n+3) c t : Int)+j ∧
  0 < (sourceCount (m+3) e u : Int)+k ∧
  (((sourceCount (n+3) c t : Int)+j < (sourceCount (m+3) e u : Int)+k) ↔
    CounterLexLT n m j k (wordValue (leaderWord n c) t) (wordValue (leaderWord m e) u)) ∧
  (((sourceCount (n+3) c t : Int)+j = (sourceCount (m+3) e u : Int)+k) ↔
    wordValue (leaderWord n c) t = wordValue (leaderWord m e) u ∧ n = m ∧ j = k)

/-- Strict, equality and weak word guards with arbitrary interiors and signed
outer shifts. Both original raw inputs and every dynamic domain are retained. -/
def CounterWordGuardCorrect : Prop := ∀ D : Nat, ∀ A B : Word,
  WordAllowed D A → WordAllowed D B → ∀ n m c e : Nat, ∀ j k : Int,
  n+3 ≤ D → m+3 ≤ D → ∀ x y : Nat,
  guardTail A B n m c e j k ≤ x → guardTail A B n m c e j k ≤ y →
  let L := A ++ [counterLetter (n+3) c, shiftLetter j]
  let R := B ++ [counterLetter (m+3) e, shiftLetter k]
  let U := wordValue (A ++ leaderWord n c) x
  let V := wordValue (B ++ leaderWord m e) y
  WordDomain L x ∧ WordDomain R y ∧
  WordAllowed D (A ++ leaderWord n c) ∧ WordAllowed D (B ++ leaderWord m e) ∧
  WordDomain (A ++ leaderWord n c) x ∧ WordDomain (B ++ leaderWord m e) y ∧
  (wordValue L x < wordValue R y ↔ CounterLexLT n m j k U V) ∧
  (wordValue L x = wordValue R y ↔ U = V ∧ n = m ∧ j = k) ∧
  (wordValue L x ≤ wordValue R y ↔ CounterLexLT n m j k U V ∨ (U = V ∧ n = m ∧ j = k))

/-- The recursive child retains each interior exactly once and eliminates the
outer E nodes. This is not the full guard-recursion termination theorem. -/
def CounterHeadDecrease : Prop := ∀ A B : Word, ∀ n m c e : Nat,
  counterNodes (A ++ leaderWord n c)+counterNodes (B ++ leaderWord m e)+2 =
    counterNodes (A ++ [counterLetter (n+3) c])+counterNodes (B ++ [counterLetter (m+3) e])

/-- Actual constructor and actual cutoffs, uniformly in complete words and all
rank, mass and signed-shift parameters. -/
def GuardPrograms : Prop :=
  Primrec (fun p : Nat × Nat => leaderWord p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => leaderTail p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Int × Int => scalarTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Primrec (fun p : Word × Word × Nat × Nat × Nat × Nat × Int × Int =>
    guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)

end LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Targets
