module
public import LogicLineages.OrdinalComparison.PolynomialOrdinalDefinitions
public import LogicLineages.OrdinalComparison.ConstantBudgetTargets

@[expose] public section

/-! Actual polynomial-state/partition-vector suppliers for paper10 lem:fixed.
The finite-tail coefficient is retained as coordinate zero with weight one.
The normal notation map is literal and fixed before proofs. Completeness is
for every actual ordinal below omega^d, not sampled/generated states only. -/

namespace LogicLineages.OrdinalComparison.Targets

def PolynomialRawNoteNormalBoundNorm : Prop :=
  ∀ d : Nat, ∀ a : Fin d → Nat,
    ONote.NF (polynomialRawNote d a) ∧
      (polynomialRawNote d a).repr < Ordinal.omega0 ^ (d : Ordinal) ∧
      Vendor.R1.treeWeight (polynomialRawNote d a) = restrictedPartitionWeight a

def PolynomialRawNoteInjective : Prop :=
  ∀ d : Nat, Function.Injective (polynomialRawNote d)

def PolynomialRawNoteOrdinalComplete : Prop :=
  ∀ d : Nat, ∀ x : Ordinal.{0}, x < Ordinal.omega0 ^ (d : Ordinal) →
    ∃ a : Fin d → Nat, (polynomialRawNote d a).repr = x

def FullActualPolynomialNormPartitionCardinality : Prop :=
  PolynomialRawNoteNormalBoundNorm ∧ PolynomialRawNoteInjective ∧
    PolynomialRawNoteOrdinalComplete ∧ ActualPolynomialNormPartitionCardinality

end LogicLineages.OrdinalComparison.Targets
