module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.Targets
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionTargets
public import LogicLineages.OrdinalComparison.SignedKernelDomainTargets
public import LogicLineages.OrdinalComparison.SmallKernelsTargets
public import LogicLineages.OrdinalComparison.CounterSourceTheoremTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.TargetChecks

/-- Comparator independent of any new proof: every numerical recursion clause
matches the previously frozen exact supplier, including its child domain. -/
example : Targets.CorrectedKernelRecursion =
    (LogicLineages.OrdinalComparison.Targets.ActualOmegaSuffixKernel ∧
    LogicLineages.OrdinalComparison.Targets.ActualOmegaSquaredSuffixCount ∧
    LogicLineages.OrdinalComparison.Targets.ActualFiniteKernelBlockRecursion ∧
    LogicLineages.OrdinalComparison.Targets.ActualFiniteSignedBlockRecursion ∧
    LogicLineages.OrdinalComparison.Targets.ActualFiniteQuadraticShift ∧
    LogicLineages.OrdinalComparison.Targets.ActualFiniteKernelPrograms) := rfl

/-- No counter clause or parameter is dropped during corrected-source assembly. -/
example : Targets.CorrectedCounterSource =
    (CounterSourceTheorem.Targets.WholeCounterLemma ∧
      CounterSourceTheorem.Targets.UniformTailPrograms) := rfl

example : Targets.SourceProcessBridge = (∀ d c t : Nat, 1 ≤ d → c+d+1 ≤ t →
  sourceCount d c t = actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t ∧
  sourceValue d c t = actualSuffixKernel (Ordinal.omega0 ^ (d : Ordinal)) c t ∧
  (∀ i : Nat, 1 ≤ i → i ≤ sourceCount d c t →
    sourceState d c t i = actualControlledStateAfter (compensatedPrefixControl c)
      (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t) i) ∧
  0 < sourceCount d c t ∧
  sourceState d c t (sourceCount d c t) < Ordinal.omega0 ∧
  (∀ i : Nat, i < sourceCount d c t → Ordinal.omega0 ≤ sourceState d c t i) ∧
  (∀ i : Nat, 1 ≤ i → i ≤ sourceCount d c t →
    c + actualOrdinalNorm (sourceState d c t i) = (Phi^[i]) t)) := rfl

example : admissibleSignedPair 1 (-1) = False := by simp [admissibleSignedPair]
example : admissibleSignedPair 2 (-1) = True := by simp [admissibleSignedPair]

example : Targets.SignedDomainContract =
    (LogicLineages.OrdinalComparison.Targets.DegreeOneSignedDomain ∧
    LogicLineages.OrdinalComparison.Targets.DegreeOneNegativeDepthObstruction ∧
    (∀ d c : Nat, ∀ j : Int, admissibleSignedPair d j → ∀ t : Nat,
      correctedSignedKernelThreshold d c j 1 ≤ t → 0 < signedKernelDepth d c j t)) := rfl

example : Targets.CorrectedKernelResidues =
    ((∀ d c : Nat, ∀ j : Int, admissibleSignedPair d j → ∀ m : Nat, 1 ≤ m →
      ∀ t : Nat, residueTail d c j m ≤ t →
        0 < signedKernelDepth d c j t ∧
        Nat.ModEq m (rawSignedKernelValue d c j t) (fastControlResidue m) ∧
        Nat.ModEq m (sourceCount d c t)
          (restrictedPartitionCount d (kernelModularDifference (restrictedPartitionPeriod d m)
            (fastControlResidue (restrictedPartitionPeriod d m)) c)) ∧
        kernelCounterResidue d c m < m ∧
        sourceCount d c t % m = kernelCounterResidue d c m) ∧
    Primrec (fun z : Nat × Nat × Nat => kernelCounterResidue z.1 z.2.1 z.2.2) ∧
    (∀ j : Int, Primrec (fun z : Nat × Nat × Nat => residueTail z.1 z.2.1 j z.2.2))) := rfl

end LogicLineages.OrdinalComparison.KernelSourceCompletion.TargetChecks
