module
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion AdjacentRangeWordGuardCompletion

/-- Expose any higher X rank to the opposite lower X rank and strip both
exposed heads. All retained unsigned heads stay attached to the original x. -/
def MixedKernelGuard : Prop := ∀ D : Nat, ∀ A B : Word,
  WordAllowed D A → WordAllowed D B → ∀ n m c e : Nat, ∀ j k a b : Int,
  n+m+4 ≤ D → ∀ x y : Nat, MixedRangeWordGuardCompletion.kernelGuardTail A B n m c e j k a b ≤ x →
  MixedRangeWordGuardCompletion.kernelGuardTail A B n m c e j k a b ≤ y →
  let L := A++[kernelLetter (n+m+4) c j,shiftLetter a]
  let R := B++[kernelLetter (n+3) e k,shiftLetter b]
  let U := wordValue (retainedWord A (n+1) m c) x
  let V := wordValue B y
  WordDomain L x ∧ WordDomain R y ∧
  WordAllowed D (retainedWord A (n+1) m c) ∧ WordDomain (retainedWord A (n+1) m c) x ∧
  (wordValue L x < wordValue R y ↔ ShiftedEqualRankWordGuardCompletion.KernelShiftLexLT c e j k a b U V) ∧
  (wordValue L x = wordValue R y ↔ U = V ∧ c = e ∧ j = k ∧ a = b) ∧
  (wordValue L x ≤ wordValue R y ↔
    ShiftedEqualRankWordGuardCompletion.KernelShiftLexLT c e j k a b U V ∨
      (U = V ∧ c = e ∧ j = k ∧ a = b))

/-- Every higher X rank against literal V, using the genuine ceiling-adjusted
quadratic endpoint and preserving all signed depth/outer-shift ties. -/
def MixedQuadraticGuard : Prop := ∀ D : Nat, ∀ A B : Word,
  WordAllowed D A → WordAllowed D B → ∀ m c : Nat, ∀ j k a b : Int, m+3 ≤ D →
  ∀ x y : Nat, MixedRangeWordGuardCompletion.quadraticGuardTail A B m c j k a b ≤ x →
  MixedRangeWordGuardCompletion.quadraticGuardTail A B m c j k a b ≤ y →
  let L := A++[kernelLetter (m+3) c j,shiftLetter a]
  let R := B++[quadraticLetter k,shiftLetter b]
  let U := wordValue (retainedWord A 0 m c) x
  let V := wordValue B y
  let q := j-(((c+1)/2 : Nat) : Int)
  WordDomain L x ∧ WordDomain R y ∧
  WordAllowed D (retainedWord A 0 m c) ∧ WordDomain (retainedWord A 0 m c) x ∧
  (wordValue L x < wordValue R y ↔ QuadraticWordGuardCompletion.ShiftLexLT q k a b U V) ∧
  (wordValue L x = wordValue R y ↔ U = V ∧ q = k ∧ a = b) ∧
  (wordValue L x ≤ wordValue R y ↔
    QuadraticWordGuardCompletion.ShiftLexLT q k a b U V ∨ (U = V ∧ q = k ∧ a = b))

/-- Exact local count identity: delete the opposite exposed rank, retain the
original highest rank, and introduce one occurrence of each strictly intermediate
rank. E count is unchanged. This is not a global termination theorem. -/
def MixedHeadDecrease : Prop := ∀ A B : Word, ∀ n m c e : Nat, ∀ j k : Int,
  counterNodes (retainedWord A n m c)+counterNodes B =
    counterNodes (A++[kernelLetter (n+m+3) c j])+
      counterNodes (B++[SourceRangeExpansion.lowerHead n e k]) ∧
  ∀ r : Nat, rangeNodes r (retainedWord A n m c)+rangeNodes r B+(if r=n+2 then 1 else 0) =
    rangeNodes r (A++[kernelLetter (n+m+3) c j])+
      rangeNodes r (B++[SourceRangeExpansion.lowerHead n e k])+
        (if n+2<r ∧ r<n+m+3 then 1 else 0)

/-- Actual retained-word construction and both finite-gap cutoff programs. -/
def GuardPrograms : Prop :=
  Primrec (fun p : Word × Nat × Nat × Nat => retainedWord p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Word × Word × Nat × Nat × Nat × Nat × Int × Int × Int × Int =>
    MixedRangeWordGuardCompletion.kernelGuardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2) ∧
  Primrec (fun p : Word × Word × Nat × Nat × Int × Int × Int × Int =>
    MixedRangeWordGuardCompletion.quadraticGuardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)

end LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Targets
