module
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion

/-- Literal source-head factorization with actual preimage-word admission and
domain. Phi, quadratic V and all admitted signed higher X heads are covered. -/
def RangeHeadPreimage : Prop := ∀ D a t, LetterAllowed D a → RangeHead a →
  RangePhiFactorization.factorTail a ≤ t →
  WordAllowed D (preimageWord a) ∧ WordDomain (preimageWord a) t ∧
  LetterDomain a t ∧ letterValue a t = Phi (wordValue (preimageWord a) t)

/-- One exact guard for a source counter against any ordinary range head,
with arbitrary original interior words and arbitrary signed outer shifts. -/
def CounterRangeWordGuardCorrect : Prop := ∀ D : Nat, ∀ A B : Word, ∀ a : Letter,
  WordAllowed D A → WordAllowed D B → LetterAllowed D a → RangeHead a →
  ∀ n c : Nat, ∀ j k : Int, n+3 ≤ D → ∀ x y : Nat,
  CounterRangeWordGuardCompletion.guardTail A B n c a j k ≤ x →
  CounterRangeWordGuardCompletion.guardTail A B n c a j k ≤ y →
  let L := A ++ [counterLetter (n+3) c,shiftLetter j]
  let R := B ++ [a,shiftLetter k]
  let U := wordValue (A ++ leaderWord n c) x
  let V := wordValue (rangeInputWord B a) y
  WordDomain L x ∧ WordDomain R y ∧
  WordAllowed D (A ++ leaderWord n c) ∧ WordDomain (A ++ leaderWord n c) x ∧
  WordAllowed D (rangeInputWord B a) ∧ WordDomain (rangeInputWord B a) y ∧
  (wordValue L x < wordValue R y ↔ U ≤ V) ∧
  (wordValue L x = wordValue R y ↔ False) ∧
  (wordValue L x ≤ wordValue R y ↔ U ≤ V) ∧
  (wordValue R y < wordValue L x ↔ V < U)

/-- Every recursive child retains both interiors once and removes exactly the
outer E occurrence, regardless of which ordinary range tag is on the right. -/
def CounterHeadDecrease : Prop := ∀ A B : Word, ∀ a : Letter, RangeHead a → ∀ n c : Nat,
  counterNodes (A ++ leaderWord n c)+counterNodes (rangeInputWord B a)+1 =
    counterNodes (A ++ [counterLetter (n+3) c])+counterNodes (B ++ [a])

/-- The actual source-code preimage constructor and combined cutoff are
uniformly primitive recursive, including their total malformed behavior. -/
def GuardPrograms : Prop := Primrec preimageWord ∧
  Primrec (fun p : Word × Letter => rangeInputWord p.1 p.2) ∧
  Primrec (fun p : Word × Word × Nat × Nat × Letter × Int × Int =>
    CounterRangeWordGuardCompletion.guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1
      p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2)

end LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Targets
