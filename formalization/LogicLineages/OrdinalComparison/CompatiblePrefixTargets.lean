module
public import LogicLineages.OrdinalComparison.CompatiblePrefixDefinitions

@[expose] public section

/-! Independent actual source suppliers for paper07 lem:prefix and the
retained-prefix clause of paper10 lem:fixed. The compatibility predicates
literally inspect the ordinary actual CNF and allow equal boundary exponents.
These maximum/norm suppliers alone do NOT assert a first-finite-cut trace
conjugacy or complete either full numbered source lemma. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualMinExponentDivisibility : Prop :=
  ∀ k : Ordinal.{0}, k < epsilonZero → ∀ e : Ordinal.{0},
    actualMinExponentAtLeast k e ↔ Ordinal.omega0 ^ e ∣ k

def RawDivisiblePrefixNormAddition : Prop :=
  ∀ a b : NONote, ∀ e : Ordinal.{0}, Ordinal.omega0 ^ e ∣ a.1.repr →
    b.1.repr < Ordinal.omega0 ^ (e + 1) →
      Vendor.R1.treeWeight (a.1 + b.1) = Vendor.R1.treeWeight a.1 + Vendor.R1.treeWeight b.1

def ActualDivisiblePrefixNormAddition : Prop :=
  ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero → ∀ e : Ordinal.{0},
    Ordinal.omega0 ^ e ∣ k → r < Ordinal.omega0 ^ (e + 1) →
      k + r < epsilonZero ∧ actualOrdinalNorm (k + r) = actualOrdinalNorm k + actualOrdinalNorm r

def ActualDivisiblePrefixMaximum : Prop :=
  ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero → 0 < r →
    ∀ e : Ordinal.{0}, actualMinExponentAtLeast k e → r < Ordinal.omega0 ^ (e + 1) →
      ∀ b : Nat, actualOrdinalNorm k ≤ b →
        actualMaximumPredecessor (k + r) b =
          k + actualMaximumPredecessor r (b - actualOrdinalNorm k)

def ActualCompatiblePrefixMaximum : Prop :=
  ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero → Order.IsSuccLimit r →
    actualCNFPrefixCompatible k r → ∀ b : Nat, actualOrdinalNorm k ≤ b →
      actualMaximumPredecessor (k + r) b =
        k + actualMaximumPredecessor r (b - actualOrdinalNorm k)

def CompensatedPrefixControlBounds : Prop :=
  ∀ c : Nat, Monotone (compensatedPrefixControl c) ∧
    ∀ n : Nat, Phi n ≤ compensatedPrefixControl c n ∧ n < compensatedPrefixControl c n

end LogicLineages.OrdinalComparison.Targets
