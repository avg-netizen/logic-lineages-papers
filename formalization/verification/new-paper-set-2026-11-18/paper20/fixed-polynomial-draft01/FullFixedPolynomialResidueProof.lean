module
public import LogicLineages.CartierObserverCurrent.FullFixedPolynomialResidueTargets
public import LogicLineages.OrdinalComparison.KernelCounterResidueProof
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullFixedPolynomialResidue
open LogicLineages.OrdinalComparison

theorem modularDifference : Targets.ModularDifference := by
  intro Q r c hQ _
  have hle : c % Q ≤ r + Q := (Nat.mod_lt c hQ).le.trans (Nat.le_add_left Q r)
  have hcast : ((r + Q - c % Q : Nat) : Int) = (r : Int) + Q - (c % Q : Nat) := by
    rw [Int.ofNat_sub hle, Nat.cast_add]
  have h : (((r + Q - c % Q) % Q : Nat) : Int) = ((r : Int) - c) % Q := by
    rw [Int.natCast_emod, hcast]
    simp [Int.sub_emod, Int.add_emod, Int.natCast_emod]
  simpa only [kernelModularDifference, Int.toNat_natCast] using congrArg Int.toNat h

theorem sourceCongruence : Targets.SourceCongruence := by
  intro c d m hd hm t ht
  have hpos := KernelCounterCalibrationProof.kernelPeriodPositive d m hd hm
  have h := KernelCounterResidueProof.actualKernelCounterCongruence d c m hd hm t
    (by simpa only [kernelCounterThreshold, restrictedPartitionPeriod, Nat.max_comm] using ht)
  rw [modularDifference _ _ c hpos.1 hpos.2] at h
  exact h

attribute [local irreducible] Nat.sqrt Nat.unpair encodedSuffixKernelCount encodedNatNote

theorem exactEvaluation : Targets.ExactEvaluation := by
  have hargs : Primrec (fun p : Nat × Nat × Nat => (encodedNatNote p.1,p.2.1,p.2.2)) :=
    (encodedKernelBuildersPrimitiveRecursive.1.comp Primrec.fst).pair Primrec.snd
  refine ⟨Computable.comp encodedSuffixKernelComputable.1 hargs.to_comp, ?_⟩
  intro d c t hd ht
  let eta : NONote := ⟨ONote.ofNat d,ONote.nf_ofNat d⟩
  have hpos : 0 < eta.1.repr := by
    simp only [eta,ONote.repr_ofNat]
    exact_mod_cast (by omega : 0 < d)
  have hdom : c + actualOrdinalNorm (Ordinal.omega0 ^ eta.1.repr) ≤ t := by
    simp only [eta,ONote.repr_ofNat,power_norm]
    exact ht
  have h := (encodedSuffixKernelCorrect eta hpos c t hdom).1
  rw [encodedNatNoteCorrect d]
  simpa only [eta,ONote.repr_ofNat] using h

theorem completeFixedPolynomialResidue : Targets.CompleteFixedPolynomialResidue :=
  ⟨modularDifference, sourceCongruence, exactEvaluation⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullFixedPolynomialResidue
end LogicLineages.CartierObserverCurrent.FullFixedPolynomialResidue
