module
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterRangeWordGuardCompletion CounterWordGuardCompletion

/-- Literal Phi values with arbitrary signed outer shifts. All non-tie gaps
are paid, and integer positivity precedes natural totalization. -/
def ShiftedPhiOrder : Prop := ∀ j k : Int, ∀ u v : Nat,
  scalarTail j k ≤ u → scalarTail j k ≤ v →
  0 < (Phi u : Int)+j ∧ 0 < (Phi v : Int)+k ∧
  ((Phi u : Int)+j < (Phi v : Int)+k ↔ PreimageLexLT j k u v) ∧
  ((Phi u : Int)+j = (Phi v : Int)+k ↔ u = v ∧ j = k) ∧
  ((Phi u : Int)+j ≤ (Phi v : Int)+k ↔ PreimageLexLT j k u v ∨ (u = v ∧ j = k))

/-- Cancel a shifted Phi against any shifted ordinary source range head. The
literal preimage word is identity for Phi or the coherent predecessor for V/X.
Original raw inputs remain shared, with all generated and original domains. -/
def PhiRangeWordGuardCorrect : Prop := ∀ D : Nat, ∀ A B : Word, ∀ a : Letter,
  WordAllowed D A → WordAllowed D B → LetterAllowed D a → RangeHead a →
  ∀ j k : Int, ∀ x y : Nat,
  ShiftedPhiRangeWordGuardCompletion.guardTail A B a j k ≤ x →
  ShiftedPhiRangeWordGuardCompletion.guardTail A B a j k ≤ y →
  let L := A ++ [phiLetter,shiftLetter j]
  let R := B ++ [a,shiftLetter k]
  let U := wordValue A x
  let V := wordValue (rangeInputWord B a) y
  WordDomain L x ∧ WordDomain R y ∧
  WordAllowed D (rangeInputWord B a) ∧ WordDomain (rangeInputWord B a) y ∧
  (wordValue L x < wordValue R y ↔ PreimageLexLT j k U V) ∧
  (wordValue L x = wordValue R y ↔ U = V ∧ j = k) ∧
  (wordValue L x ≤ wordValue R y ↔ PreimageLexLT j k U V ∨ (U = V ∧ j = k))

/-- This child preserves the E count and strictly removes rank-one nodes.
Both interiors are retained once; no global termination theorem is asserted. -/
def HeadDecrease : Prop := ∀ A B : Word, ∀ a : Letter, RangeHead a →
  counterNodes A+counterNodes (rangeInputWord B a) =
    counterNodes (A++[phiLetter])+counterNodes (B++[a]) ∧
  phiNodes A+phiNodes (rangeInputWord B a) <
    phiNodes (A++[phiLetter])+phiNodes (B++[a])

/-- The actual cutoff, including both preimage construction and domain
factorization, is primitive recursive in all word/head/shift codes. -/
def GuardPrograms : Prop := Primrec (fun p : Int × Int => scalarTail p.1 p.2) ∧
  Primrec (fun p : Word × Word × Letter × Int × Int =>
    ShiftedPhiRangeWordGuardCompletion.guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Targets
