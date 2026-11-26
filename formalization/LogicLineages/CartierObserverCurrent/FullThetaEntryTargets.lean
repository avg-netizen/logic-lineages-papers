module
public import LogicLineages.OrdinalComparison.ThetaEntryTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullThetaEntry.Targets
open LogicLineages.OrdinalComparison

def ExplicitFamily : Prop :=
  ∀ v : Nat, 4 ≤ v →
    let Θ := Ordinal.omega0 ^ (Ordinal.omega0 + 1)
    let a := Θ + ((v - 4 : Nat) : Ordinal)
    let u := Phi v
    let q := (u - 1) / 3
    let p := Ordinal.omega0 ^ Ordinal.omega0 * ((q - 1 : Nat) : Ordinal)
    a < epsilonZero ∧ actualOrdinalNorm a = v ∧ actualLimitPart a = Θ ∧
      1 ≤ q ∧ actualDescentStep a = Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal) + 1 ∧
      actualDescentStep a = p + (Ordinal.omega0 ^ Ordinal.omega0 + 1) ∧
      p < epsilonZero ∧ actualOrdinalNorm p = u - 4 ∧
      actualMinExponentAtLeast p Ordinal.omega0 ∧ actualOrdinalNorm (actualDescentStep a) = u

def CompleteEntry : Prop :=
  LogicLineages.OrdinalComparison.Targets.ActualPhiResidueThree ∧
    LogicLineages.OrdinalComparison.Targets.ActualThetaEntryWitness ∧ ExplicitFamily
end LogicLineages.CartierObserverCurrent.FullThetaEntry.Targets
