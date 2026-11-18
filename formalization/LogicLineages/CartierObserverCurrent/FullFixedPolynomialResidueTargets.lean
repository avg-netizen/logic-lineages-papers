module
public import LogicLineages.OrdinalComparison.KernelCounterResidueTargets
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullFixedPolynomialResidue.Targets
open LogicLineages.OrdinalComparison

/-- Integer modular subtraction, including c greater than the representative. -/
def ModularDifference : Prop :=
  ∀ Q r c : Nat, 0 < Q → r < Q →
    kernelModularDifference Q r c = (((r : Int) - (c : Int)) % (Q : Int)).toNat

/-- Complete printed standard-control congruence with literal factorial threshold. -/
def SourceCongruence : Prop :=
  ∀ c d m : Nat, 1 ≤ d → 1 ≤ m → ∀ t : Nat,
    max (c + d + 1) (d.factorial * m ^ (d - 1)) ≤ t →
    Nat.ModEq m (actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t)
      (restrictedPartitionCount d
        ((((fastControlResidue (d.factorial * m ^ (d - 1)) : Nat) : Int) -
          (c : Int)) % (d.factorial * m ^ (d - 1) : Nat)).toNat)

/-- A genuine total computable numerical evaluator, correct on all valid inputs,
including every exceptional input below the asymptotic residue threshold. -/
def ExactEvaluation : Prop :=
  Computable (fun p : Nat × Nat × Nat =>
    encodedSuffixKernelCount (encodedNatNote p.1) p.2.1 p.2.2) ∧
  ∀ d c t : Nat, 1 ≤ d → c + d + 1 ≤ t →
    encodedSuffixKernelCount (encodedNatNote d) c t =
      actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t

def CompleteFixedPolynomialResidue : Prop :=
  ModularDifference ∧ SourceCongruence ∧ ExactEvaluation
end LogicLineages.CartierObserverCurrent.FullFixedPolynomialResidue.Targets
