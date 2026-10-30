module

public import LogicLineages.OrdinalComparison.SignedKernelDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Corrected/genuine-domain suppliers only. The unchanged source assertion of
an eventual positive depth for d=1 and every signed j is not promoted. -/
def FiniteDegreeCounterLowerBound : Prop :=
  (∀ d c t : Nat, 2 ≤ d → c + d + 1 ≤ t →
    actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t ≤
      actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t) ∧
  ∀ d c k t : Nat, 2 ≤ d → max (c + d + 1) (c + 2 * k + 3) ≤ t →
    k < actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t

def DegreeOneSignedDomain : Prop :=
  ∀ c t : Nat, c + 2 ≤ t → ∀ j : Int,
    signedKernelDepth 1 c j t = 1 + j ∧ (0 < signedKernelDepth 1 c j t ↔ 0 ≤ j)

def DegreeOneNegativeDepthObstruction : Prop :=
  ∀ c : Nat, ∀ j : Int, j < 0 →
    ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t → c + 2 ≤ t → 0 < signedKernelDepth 1 c j t

def GenuineSignedKernelResidueAndCoherence : Prop :=
  ∀ d c : Nat, ∀ j : Int, ∀ t : Nat, 0 < signedKernelDepth d c j t →
    rawSignedKernelValue d c (j + 1) t = Phi (rawSignedKernelValue d c j t) ∧
      ∀ m : Nat, 1 ≤ m → m ≤ t →
        Nat.ModEq m (rawSignedKernelValue d c j t) (fastControlResidue m)

def CorrectedSignedKernelResidues : Prop :=
  ∀ d c : Nat, ∀ j : Int, (2 ≤ d ∨ (d = 1 ∧ 0 ≤ j)) →
    ∀ m : Nat, 1 ≤ m → ∀ t : Nat, correctedSignedKernelThreshold d c j m ≤ t →
      0 < signedKernelDepth d c j t ∧
        Nat.ModEq m (rawSignedKernelValue d c j t) (fastControlResidue m)

def FixedSignedKernelThresholdPrimitiveRecursive : Prop :=
  ∀ j : Int, Primrec (fun z : Nat × Nat × Nat => correctedSignedKernelThreshold z.1 z.2.1 j z.2.2)

end LogicLineages.OrdinalComparison.Targets
