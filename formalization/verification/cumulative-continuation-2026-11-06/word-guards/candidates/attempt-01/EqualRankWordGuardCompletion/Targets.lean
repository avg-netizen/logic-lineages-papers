module
public import LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Strict order on every input above the existing exact uniform threshold. -/
def KernelOrderCorrect : Prop :=
  ∀ d c e : Nat, ∀ j k : Int, 3 ≤ d → ∀ t u : Nat,
    equalityTail d c e j k ≤ t → equalityTail d c e j k ≤ u →
    (sourceSignedValue d c j t < sourceSignedValue d e k u ↔
      KernelLexLT c e j k t u)

/-- Simultaneous literal domains and exact three-way guard lowering for
arbitrary allowed interior compositions, with their raw variables retained.
The right-hand comparisons have removed both outer rank-d occurrences. -/
def EqualRankWordGuardCorrect : Prop :=
  ∀ D : Nat, ∀ A B : Word, WordAllowed D A → WordAllowed D B →
  ∀ d c e : Nat, ∀ j k : Int, 3 ≤ d → d ≤ D → ∀ x y : Nat,
    guardTail A B d c e j k ≤ x → guardTail A B d c e j k ≤ y →
    WordDomain (A ++ [kernelLetter d c j]) x ∧
    WordDomain (B ++ [kernelLetter d e k]) y ∧
    (wordValue (A ++ [kernelLetter d c j]) x <
      wordValue (B ++ [kernelLetter d e k]) y ↔
      KernelLexLT c e j k (wordValue A x) (wordValue B y)) ∧
    (wordValue (A ++ [kernelLetter d c j]) x =
      wordValue (B ++ [kernelLetter d e k]) y ↔
      wordValue A x = wordValue B y ∧ c = e ∧ j = k) ∧
    (wordValue (A ++ [kernelLetter d c j]) x ≤
      wordValue (B ++ [kernelLetter d e k]) y ↔
      KernelLexLT c e j k (wordValue A x) (wordValue B y) ∨
        (wordValue A x = wordValue B y ∧ c = e ∧ j = k))

/-- The actual emitted threshold is primitive recursive in every raw code
parameter, including both complete word lists and arbitrary signed indices. -/
def EqualRankWordGuardPrograms : Prop :=
  Primrec (fun p : Word × Word × Nat × Nat × Nat × Int × Int =>
    guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 p.2.2.2.2.2.2)

end LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Targets
