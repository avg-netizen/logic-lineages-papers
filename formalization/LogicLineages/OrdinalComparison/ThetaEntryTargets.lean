module
public import LogicLineages.OrdinalComparison.OmegaBlockTargets
public import LogicLineages.OrdinalComparison.HeadWindowTargets

@[expose] public section

/-! Full actual source paper10 lem:entry (paper.tex353–369). An entry is an
actual source ordinal whose limit part is omega^(omega+1); no independent
entry-value oracle, hypothetical retained mass or assumed maximum is used. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualPhiResidueThree : Prop := ∀ v : Nat, Nat.ModEq 3 (Phi v) 1

def ActualOmegaMultipleFacts : Prop :=
  ∀ q : Nat, Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal) < epsilonZero ∧
    actualOrdinalNorm (Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal)) = 3 * q ∧
      actualMinExponentAtLeast (Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal)) Ordinal.omega0

def ActualThetaFacts : Prop :=
  Ordinal.omega0 ^ (Ordinal.omega0 + 1) < epsilonZero ∧
    Order.IsSuccLimit (Ordinal.omega0.{0} ^ (Ordinal.omega0.{0} + 1)) ∧
      actualOrdinalNorm (Ordinal.omega0 ^ (Ordinal.omega0 + 1)) = 4

def ActualThetaBudgetMaximum : Prop :=
  ∀ u : Nat, 4 ≤ u → Nat.ModEq 3 u 1 →
    actualMaximumPredecessor (Ordinal.omega0 ^ (Ordinal.omega0 + 1)) u =
      Ordinal.omega0 ^ Ordinal.omega0 * (((u - 1) / 3 : Nat) : Ordinal) + 1

def ActualThetaEntryWitness : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    actualLimitPart a = Ordinal.omega0 ^ (Ordinal.omega0 + 1) →
    let v := actualOrdinalNorm a
    let u := Phi v
    let q := (u - 1) / 3
    let p := Ordinal.omega0 ^ Ordinal.omega0 * ((q - 1 : Nat) : Ordinal)
    4 ≤ v ∧ Nat.ModEq 3 u 1 ∧ 1 ≤ q ∧
      actualDescentStep a = Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal) + 1 ∧
      actualDescentStep a = p + (Ordinal.omega0 ^ Ordinal.omega0 + 1) ∧
      p < epsilonZero ∧ actualOrdinalNorm p = u - 4 ∧
      actualMinExponentAtLeast p Ordinal.omega0 ∧
      actualOrdinalNorm (actualDescentStep a) = u ∧
      actualOrdinalNorm (Ordinal.omega0 ^ Ordinal.omega0 + 1) = 4

def FullActualThetaEntry : Prop :=
  ActualPhiResidueThree ∧ ActualOmegaMultipleFacts ∧ ActualThetaFacts ∧
    ActualThetaBudgetMaximum ∧ ActualThetaEntryWitness

end LogicLineages.OrdinalComparison.Targets
