module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:successor, lines 658–682: actual retained-block traces.
The first finite cut is the literal controlled count, not an input oracle. -/
def ActualCompensatedControlComposition : Prop :=
  ∀ c w : Nat, prefixRemainderControl (compensatedPrefixControl c) w =
    compensatedPrefixControl (c + w)

def ActualSuccessorKernelFirstStep : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma →
    Ordinal.omega0 ^ gamma * Ordinal.omega0 < epsilonZero → ∀ c t : Nat,
      let theta := Ordinal.omega0 ^ gamma
      let L := theta * Ordinal.omega0
      let w := actualOrdinalNorm theta
      c + w + actualOrdinalNorm L ≤ t →
        actualControlledStateAfter (compensatedPrefixControl c)
          (actualSuffixKernelInitial L c t) 1 =
        theta + actualControlledStateAfter (compensatedPrefixControl (c + w))
          (actualSuffixKernelInitial L (c + w) t) 1

def ActualSuccessorKernelCut : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma →
    Ordinal.omega0 ^ gamma * Ordinal.omega0 < epsilonZero → ∀ c t : Nat,
      let theta := Ordinal.omega0 ^ gamma
      let L := theta * Ordinal.omega0
      let w := actualOrdinalNorm theta
      c + w + actualOrdinalNorm L ≤ t →
        let E := actualSuffixKernelCount L (c + w) t
        let K := actualSuffixKernel L (c + w) t
        let outer := actualControlledStateAfter (compensatedPrefixControl c)
          (actualSuffixKernelInitial L c t)
        let inner := actualControlledStateAfter (compensatedPrefixControl (c + w))
          (actualSuffixKernelInitial L (c + w) t)
        (∀ i : Nat, 1 ≤ i → i ≤ E → outer i = theta + inner i) ∧
        c + w ≤ K ∧ E ≤ actualSuffixKernelCount L c t ∧
        outer E = actualSuffixKernelInitial theta c K

end LogicLineages.OrdinalComparison.Targets
