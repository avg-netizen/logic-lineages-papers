module
public import LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion

/-- Expand rank n+4 once and immediately compare/strip its outer rank n+3
against the opposite rank n+3. The retained higher-rank word is not independent. -/
def AdjacentKernelGuard : Prop := ∀ D : Nat, ∀ A B : Word,
  WordAllowed D A → WordAllowed D B → ∀ n c e : Nat, ∀ j k a b : Int,
  n+4 ≤ D → ∀ x y : Nat, kernelGuardTail A B n c e j k a b ≤ x →
  kernelGuardTail A B n c e j k a b ≤ y →
  let L := A++[kernelLetter (n+4) c j,shiftLetter a]
  let R := B++[kernelLetter (n+3) e k,shiftLetter b]
  let U := wordValue (innerWord A (n+1) c) x
  let V := wordValue B y
  WordDomain L x ∧ WordDomain R y ∧
  WordAllowed D (innerWord A (n+1) c) ∧ WordDomain (innerWord A (n+1) c) x ∧
  (wordValue L x < wordValue R y ↔ ShiftedEqualRankWordGuardCompletion.KernelShiftLexLT c e j k a b U V) ∧
  (wordValue L x = wordValue R y ↔ U = V ∧ c = e ∧ j = k ∧ a = b) ∧
  (wordValue L x ≤ wordValue R y ↔
    ShiftedEqualRankWordGuardCompletion.KernelShiftLexLT c e j k a b U V ∨
      (U = V ∧ c = e ∧ j = k ∧ a = b))

/-- The cubic/quadratic boundary uses V with the exact ceiling-adjusted index.
All signed shifts and literal original/generated domains are retained. -/
def CubicQuadraticGuard : Prop := ∀ D : Nat, ∀ A B : Word,
  WordAllowed D A → WordAllowed D B → ∀ c : Nat, ∀ j k a b : Int, 3 ≤ D →
  ∀ x y : Nat, quadraticGuardTail A B c j k a b ≤ x →
  quadraticGuardTail A B c j k a b ≤ y →
  let L := A++[kernelLetter 3 c j,shiftLetter a]
  let R := B++[quadraticLetter k,shiftLetter b]
  let U := wordValue (innerWord A 0 c) x
  let V := wordValue B y
  let q := j-(((c+1)/2 : Nat) : Int)
  WordDomain L x ∧ WordDomain R y ∧
  WordAllowed D (innerWord A 0 c) ∧ WordDomain (innerWord A 0 c) x ∧
  (wordValue L x < wordValue R y ↔ QuadraticWordGuardCompletion.ShiftLexLT q k a b U V) ∧
  (wordValue L x = wordValue R y ↔ U = V ∧ q = k ∧ a = b) ∧
  (wordValue L x ≤ wordValue R y ↔
    QuadraticWordGuardCompletion.ShiftLexLT q k a b U V ∨ (U = V ∧ q = k ∧ a = b))

/-- After immediate stripping, exactly the opposite lower-rank occurrence is
lost. E count and every other range-rank count, including the higher rank,
are unchanged. This local vector identity is not a global termination claim. -/
def AdjacentHeadDecrease : Prop := ∀ A B : Word, ∀ n c e : Nat, ∀ j k : Int,
  counterNodes (innerWord A n c)+counterNodes B =
    counterNodes (A++[kernelLetter (n+3) c j])+
      counterNodes (B++[SourceRangeExpansion.lowerHead n e k]) ∧
  ∀ r : Nat, rangeNodes r (innerWord A n c)+rangeNodes r B+(if r=n+2 then 1 else 0) =
    rangeNodes r (A++[kernelLetter (n+3) c j])+
      rangeNodes r (B++[SourceRangeExpansion.lowerHead n e k])

/-- Literal retained-word constructor and both composed cutoff programs. -/
def GuardPrograms : Prop :=
  Primrec (fun p : Word × Nat × Nat => innerWord p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Word × Word × Nat × Nat × Nat × Int × Int × Int × Int =>
    kernelGuardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2) ∧
  Primrec (fun p : Word × Word × Nat × Int × Int × Int × Int =>
    quadraticGuardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2)

end LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Targets
