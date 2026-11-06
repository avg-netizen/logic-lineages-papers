module
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Exact original-source equal-rank X comparison with arbitrary depth indices
and outer shifts. Both original kernel and integer-shift domains are conclusions. -/
def ShiftedKernelOrder : Prop := ∀ d c e : Nat, ∀ j k a b : Int, 3 ≤ d → ∀ t u : Nat,
  scalarTail d c e j k a b ≤ t → scalarTail d c e j k a b ≤ u →
  LetterDomain (kernelLetter d c j) t ∧ LetterDomain (kernelLetter d e k) u ∧
  0 < (sourceSignedValue d c j t : Int)+a ∧ 0 < (sourceSignedValue d e k u : Int)+b ∧
  ((sourceSignedValue d c j t : Int)+a < (sourceSignedValue d e k u : Int)+b ↔
    KernelShiftLexLT c e j k a b t u) ∧
  ((sourceSignedValue d c j t : Int)+a = (sourceSignedValue d e k u : Int)+b ↔
    t = u ∧ c = e ∧ j = k ∧ a = b) ∧
  ((sourceSignedValue d c j t : Int)+a ≤ (sourceSignedValue d e k u : Int)+b ↔
    KernelShiftLexLT c e j k a b t u ∨ (t = u ∧ c = e ∧ j = k ∧ a = b))

/-- Strip both equal-rank source heads without creating new independent inputs.
Arbitrary admitted interiors and every signed outer shift remain literal. -/
def ShiftedEqualRankWordGuardCorrect : Prop := ∀ D : Nat, ∀ A B : Word,
  WordAllowed D A → WordAllowed D B → ∀ d c e : Nat, ∀ j k a b : Int,
  3 ≤ d → d ≤ D → ∀ x y : Nat,
  guardTail A B d c e j k a b ≤ x → guardTail A B d c e j k a b ≤ y →
  let L := A ++ [kernelLetter d c j,shiftLetter a]
  let R := B ++ [kernelLetter d e k,shiftLetter b]
  WordDomain L x ∧ WordDomain R y ∧
  (wordValue L x < wordValue R y ↔ KernelShiftLexLT c e j k a b (wordValue A x) (wordValue B y)) ∧
  (wordValue L x = wordValue R y ↔ wordValue A x = wordValue B y ∧ c = e ∧ j = k ∧ a = b) ∧
  (wordValue L x ≤ wordValue R y ↔
    KernelShiftLexLT c e j k a b (wordValue A x) (wordValue B y) ∨
      (wordValue A x = wordValue B y ∧ c = e ∧ j = k ∧ a = b))

/-- Both original interiors occur once; E count is unchanged and exactly two
rank-d X occurrences are removed. This is a local count, not global termination. -/
def HeadDecrease : Prop := ∀ A B : Word, ∀ d c e : Nat, ∀ j k : Int,
  counterNodes A+counterNodes B =
    counterNodes (A++[kernelLetter d c j])+counterNodes (B++[kernelLetter d e k]) ∧
  kernelNodesAt d A+kernelNodesAt d B+2 =
    kernelNodesAt d (A++[kernelLetter d c j])+kernelNodesAt d (B++[kernelLetter d e k])

/-- Exact total-code scalar and structural cutoff programs. -/
def GuardPrograms : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Int × Int × Int × Int =>
    scalarTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) ∧
  Primrec (fun p : Word × Word × Nat × Nat × Nat × Int × Int × Int × Int =>
    guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)

end LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Targets
