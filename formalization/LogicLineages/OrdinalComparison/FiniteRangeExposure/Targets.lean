module
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteRangeExposure.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- The finite retained prefix consists only of higher unsigned X ranks,
without counters. Its genuine final child is lowerHead, including V at n=0. -/
def PrefixSyntax : Prop := ∀ D n m c : Nat, ∀ j : Int, n+m+3 ≤ D →
  WordAllowed D (exposurePrefix n m c) ∧ WordAllowed D (exposureWord n m c j) ∧
  (exposurePrefix n m c).length = m+1 ∧ counterNodes (exposurePrefix n m c) = 0 ∧
  ∀ a ∈ exposurePrefix n m c,
    a.1 = 3 ∧ n+3 ≤ a.2.1 ∧ a.2.1 ≤ n+m+3 ∧ a.2.2.2 = 0

/-- Finite repeated ORIGINAL-source expansion down to any requested lower
ordinary rank. Every actual original/emitted domain is proved on the computed
tail; no companion schedule, fresh interior value or inverse is substituted. -/
def SourceExposure : Prop := ∀ D n m c t : Nat, ∀ j : Int, n+m+3 ≤ D →
  exposureTail n m c j ≤ t →
  LetterDomain (kernelLetter (n+m+3) c j) t ∧ WordDomain (exposureWord n m c j) t ∧
  sourceSignedValue (n+m+3) c j t = wordValue (exposureWord n m c j) t

/-- Exact replacement inside arbitrary literal prefix and suffix contexts.
The raw input remains shared and exact output equality transports suffix
validity, including signed shifts, without requiring suffix monotonicity. -/
def ContextExposure : Prop := ∀ D : Nat, ∀ A S : Word, ∀ n m c : Nat, ∀ j : Int,
  WordAllowed D A → WordAllowed D S → n+m+3 ≤ D → ∀ x : Nat,
  contextTail A S n m c j ≤ x →
  WordAllowed D (A++exposureWord n m c j++S) ∧
  WordDomain (A++[kernelLetter (n+m+3) c j]++S) x ∧
  WordDomain (A++exposureWord n m c j++S) x ∧
  wordValue (A++[kernelLetter (n+m+3) c j]++S) x =
    wordValue (A++exposureWord n m c j++S) x

/-- The actual finite prefix, exposed word and recursively computed finite
maximum are uniformly primitive recursive in the rank gap and all raw codes. -/
def ExposurePrograms : Prop :=
  Primrec (fun p : Nat × Nat × Nat => exposurePrefix p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Int => exposureWord p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Int => exposureTail p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Word × Word × Nat × Nat × Nat × Int =>
    contextTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

end LogicLineages.OrdinalComparison.FiniteRangeExposure.Targets
