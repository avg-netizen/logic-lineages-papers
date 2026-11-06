module
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion

/-- Quantitative comparison of the literal source V values, with arbitrary
signed indices and both original positive-depth domains proved. -/
def QuantitativeQuadraticGap : Prop := ∀ j k : Int, ∀ K t u : Nat,
  scalarTail j k K ≤ t → scalarTail j k K ≤ u →
  0 < QuadraticSeparation.signedDepth j t ∧ 0 < QuadraticSeparation.signedDepth k u ∧
  t ≤ rawQuadraticShift j t ∧ u ≤ rawQuadraticShift k u ∧
  (CoreLexLT j k t u → rawQuadraticShift j t+K < rawQuadraticShift k u)

/-- Exact integer comparison before natural totalization. Outer shifts remain
visible in the exact-core tie; positivity is a conclusion, not a hidden premise. -/
def ShiftedQuadraticOrder : Prop := ∀ j k a b : Int, ∀ t u : Nat,
  scalarTail j k (a.natAbs+b.natAbs) ≤ t →
  scalarTail j k (a.natAbs+b.natAbs) ≤ u →
  0 < (rawQuadraticShift j t : Int)+a ∧ 0 < (rawQuadraticShift k u : Int)+b ∧
  ((rawQuadraticShift j t : Int)+a < (rawQuadraticShift k u : Int)+b ↔
    ShiftLexLT j k a b t u) ∧
  ((rawQuadraticShift j t : Int)+a = (rawQuadraticShift k u : Int)+b ↔
    t = u ∧ j = k ∧ a = b) ∧
  ((rawQuadraticShift j t : Int)+a ≤ (rawQuadraticShift k u : Int)+b ↔
    ShiftLexLT j k a b t u ∨ (t = u ∧ j = k ∧ a = b))

/-- Two quadratic source heads around arbitrary admitted words. The guard
strips both heads, retains original raw inputs and interiors, and pays all
actual positive-depth and signed-shift domains. -/
def QuadraticWordGuardCorrect : Prop := ∀ D : Nat, ∀ A B : Word,
  WordAllowed D A → WordAllowed D B → ∀ j k a b : Int, ∀ x y : Nat,
  guardTail A B j k a b ≤ x → guardTail A B j k a b ≤ y →
  let L := A ++ [quadraticLetter j,shiftLetter a]
  let R := B ++ [quadraticLetter k,shiftLetter b]
  WordDomain L x ∧ WordDomain R y ∧
  (wordValue L x < wordValue R y ↔ ShiftLexLT j k a b (wordValue A x) (wordValue B y)) ∧
  (wordValue L x = wordValue R y ↔ wordValue A x = wordValue B y ∧ j = k ∧ a = b) ∧
  (wordValue L x ≤ wordValue R y ↔
    ShiftLexLT j k a b (wordValue A x) (wordValue B y) ∨
      (wordValue A x = wordValue B y ∧ j = k ∧ a = b))

/-- The actual finite cutoff is uniformly primitive recursive in both words,
all signed depth indices and all outer shifts. -/
def GuardPrograms : Prop :=
  Primrec (fun p : Int × Int × Nat => scalarTail p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Word × Word × Int × Int × Int × Int =>
    guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

end LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Targets
