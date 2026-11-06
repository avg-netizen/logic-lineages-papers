module
public import LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion

/-- A quantitative gap, uniformly in its requested natural margin. The source
counter and the emitted source leader word are the actual compared functions. -/
def QuantitativeCounterPhiGap : Prop := ∀ n c K t v : Nat,
  counterTail n c K ≤ t → rangeTail K ≤ v →
  (sourceCount (n+3) c t+K < Phi v ↔ wordValue (leaderWord n c) t ≤ v) ∧
  (Phi v+K < sourceCount (n+3) c t ↔ v < wordValue (leaderWord n c) t)

/-- Arbitrary signed shifts do not close the paid gap. Both positive integer
values are proved before any natural-word conversion. -/
def SourceShiftedCounterPhiOrder : Prop := ∀ n c t v : Nat, ∀ j k : Int,
  counterTail n c (j.natAbs+k.natAbs) ≤ t → rangeTail (j.natAbs+k.natAbs) ≤ v →
  0 < (sourceCount (n+3) c t : Int)+j ∧ 0 < (Phi v : Int)+k ∧
  (((sourceCount (n+3) c t : Int)+j < (Phi v : Int)+k) ↔
    wordValue (leaderWord n c) t ≤ v) ∧
  (((sourceCount (n+3) c t : Int)+j = (Phi v : Int)+k) ↔ False) ∧
  (((sourceCount (n+3) c t : Int)+j ≤ (Phi v : Int)+k) ↔
    wordValue (leaderWord n c) t ≤ v) ∧
  (((Phi v : Int)+k < (sourceCount (n+3) c t : Int)+j) ↔
    v < wordValue (leaderWord n c) t)

/-- Full arbitrary-interior word guard; raw variables and correlated interior
arguments remain literal. No ordering premise on x and y is assumed. -/
def CounterPhiWordGuardCorrect : Prop := ∀ D : Nat, ∀ A B : Word,
  WordAllowed D A → WordAllowed D B → ∀ n c : Nat, ∀ j k : Int,
  n+3 ≤ D → ∀ x y : Nat,
  CounterPhiWordGuardCompletion.guardTail A B n c j k ≤ x →
  CounterPhiWordGuardCompletion.guardTail A B n c j k ≤ y →
  let L := A ++ [counterLetter (n+3) c, shiftLetter j]
  let R := B ++ [phiLetter, shiftLetter k]
  let U := wordValue (A ++ leaderWord n c) x
  WordDomain L x ∧ WordDomain R y ∧
  WordAllowed D (A ++ leaderWord n c) ∧ WordDomain (A ++ leaderWord n c) x ∧
  (wordValue L x < wordValue R y ↔ U ≤ wordValue B y) ∧
  (wordValue L x = wordValue R y ↔ False) ∧
  (wordValue L x ≤ wordValue R y ↔ U ≤ wordValue B y) ∧
  (wordValue R y < wordValue L x ↔ wordValue B y < U)

/-- Only the counter head is removed from the primary recursion measure. -/
def CounterHeadDecrease : Prop := ∀ A B : Word, ∀ n c : Nat,
  counterNodes (A ++ leaderWord n c)+counterNodes B+1 =
    counterNodes (A ++ [counterLetter (n+3) c])+counterNodes (B ++ [phiLetter])

/-- Concrete uniformly primitive-recursive threshold maps, with no supplied
bound or growth oracle. -/
def GuardPrograms : Prop :=
  Primrec (fun p : Nat × Nat × Nat => counterTail p.1 p.2.1 p.2.2) ∧
  Primrec rangeTail ∧
  Primrec (fun p : Word × Word × Nat × Nat × Int × Int =>
    CounterPhiWordGuardCompletion.guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

end LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Targets
