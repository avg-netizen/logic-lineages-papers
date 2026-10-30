module

public import LogicLineages.OrdinalComparison.KernelCounterResidueTargets
public import LogicLineages.OrdinalComparison.KernelCounterCalibrationProof
public import LogicLineages.OrdinalComparison.RestrictedPartitionEvaluationProof
public import LogicLineages.OrdinalComparison.GrowingBudgetNumericalProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelCounterResidueProof
open KernelCounterCalibrationProof RestrictedPartitionEvaluationProof

theorem actualKernelCounterCongruence : Targets.ActualKernelCounterCongruence := by
  intro d c m hd hm t ht
  let Q := restrictedPartitionPeriod d m
  let r := fastControlResidue Q
  have hQ := (kernelPeriodPositive d m hd hm).1
  have hr := (kernelPeriodPositive d m hd hm).2
  have hQt : Q ≤ t := (Nat.le_max_left _ _).trans ht
  have hct : c + d + 1 ≤ t := (Nat.le_max_right _ _).trans ht
  let S := r + Q * (c + 1)
  have hcS : c ≤ S := by
    have hmul : c + 1 ≤ Q * (c + 1) := Nat.le_mul_of_pos_left (c + 1) hQ
    dsimp [S]
    omega
  have hSr : Nat.ModEq Q S r := by simp [Nat.ModEq, S]
  let pi := Ordinal.omega0 ^ (d : Ordinal)
  let I := actualSuffixKernelInitial pi c t
  let g := compensatedPrefixControl c
  let budget := fun i : Nat => Phi (c + actualOrdinalNorm (actualControlledStateAfter g I i))
  have hstream : (fun i => budget i - c) = actualControlBudgetStream g I := rfl
  have hin := actualFiniteKernelInput d c t hd hct
  have hsch := actualFiniteKernelSchedule d c t hd hct
  have hcount : actualScheduledCount (fun i => budget i - c) I = actualSuffixKernelCount pi c t := by
    rw [hstream]
    exact hsch.1
  have hpos : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have htr := actualSuffixKernelTrace (d : Ordinal) hpos (finiteOmegaPowerBelowEpsilonZero d)
    c t (by rw [hin.1]; omega)
  have hlive : ∀ i : Nat, i < actualScheduledCount (fun j => budget j - c) I →
      c + actualOrdinalNorm (actualScheduledStateAfter (fun j => budget j - c) I i) ≤ budget i ∧
        Nat.ModEq Q (budget i) S := by
    intro i hi
    rw [hcount] at hi
    have hs : actualScheduledStateAfter (fun j => budget j - c) I i = actualControlledStateAfter g I i := by
      rw [hstream]
      exact hsch.2.1 i
    rw [hs]
    refine ⟨(self_lt_Phi _).le, ?_⟩
    have hmass : Q ≤ c + actualOrdinalNorm (actualControlledStateAfter g I i) := by
      rw [htr.2.1 i hi.le]
      exact hQt.trans (iterate_self_le (fun x => (self_lt_Phi x).le) i t)
    exact (phiShiftedConstantResidues Q hQ _ (by omega)).trans hSr.symm
  have htransfer := actualNumericalCongruentBudgetTransfer d m c S
    (t - c - actualOrdinalNorm pi) hd hm hcS budget hlive
  change Nat.ModEq m (actualScheduledCount (fun i => budget i - c) I)
    (restrictedPartitionCount d (S - c)) at htransfer
  rw [hcount] at htransfer
  exact htransfer.trans (partitionInputCongruence d m hd hm _ _
    ((kernelModularDifferenceCorrect Q r c hQ hr).2 S hcS hSr))

private theorem pr_factorial : Primrec Nat.factorial := by
  have hs : Primrec₂ (fun n v : Nat => (n + 1) * v) :=
    (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂
  apply (Primrec.nat_rec₁ 1 hs).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, Nat.factorial_succ, ih]

private theorem pr_period : Primrec₂ restrictedPartitionPeriod := by
  have hp : Primrec₂ (fun a b : Nat => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact (Primrec.nat_mul.comp (pr_factorial.comp Primrec.fst)
    (hp.comp Primrec.snd (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)))).to₂

private theorem pr_difference : Primrec (fun z : Nat × Nat × Nat =>
    kernelModularDifference z.1 z.2.1 z.2.2) :=
  Primrec.nat_mod.comp
    (Primrec.nat_sub.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)) Primrec.fst

theorem primitiveRecursiveKernelArithmetic : Targets.PrimitiveRecursiveKernelArithmetic :=
  ⟨pr_period, pr_difference⟩

theorem primitiveRecursiveKernelResidue : Targets.PrimitiveRecursiveKernelResidue := by
  have hd : Primrec (fun z : Nat × Nat × Nat => z.1) := Primrec.fst
  have hc : Primrec (fun z : Nat × Nat × Nat => z.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun z : Nat × Nat × Nat => z.2.2) := Primrec.snd.comp Primrec.snd
  have hQ := pr_period.comp hd hm
  have hr := fastControlResiduePrimitiveRecursive.comp hQ
  have hx := pr_difference.comp (hQ.pair (hr.pair hc))
  exact ⟨Primrec.nat_mod.comp (primitiveRecursivePartitionEvaluator.2.1.comp hd hx) hm,
    Primrec.nat_max.comp hQ (Primrec.succ.comp (Primrec.nat_add.comp hc hd))⟩

theorem effectiveActualKernelCounterResidue : Targets.EffectiveActualKernelCounterResidue := by
  intro d c m hd hm
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  intro t ht
  have h := actualKernelCounterCongruence d c m hd hm t ht
  change _ % m = restrictedPartitionEval d _ % m
  rw [restrictedPartitionEvaluatorExact]
  exact h

end LogicLineages.OrdinalComparison.KernelCounterResidueProof
