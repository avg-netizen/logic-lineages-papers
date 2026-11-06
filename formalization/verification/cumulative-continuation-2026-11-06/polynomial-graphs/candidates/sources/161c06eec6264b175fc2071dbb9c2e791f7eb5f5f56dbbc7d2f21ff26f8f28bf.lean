module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadExponentProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordSemanticProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadCodeCalibrationProof
import LogicLineages.OrdinalComparison.PeakWordProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.PolynomialPartitionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadSourceProof
open WordAlgebraProof

private theorem finite_power_norm (d : Nat) :
    actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
  simpa only [Nat.cast_one, mul_one, Nat.mul_one] using
    (actualFiniteMonomialFacts d 1).2.1

private theorem mapped_run (w : List (ONote × Nat)) :
    (∀ p ∈ w, p.1 = ONote.ofNat (Vendor.R1.treeWeight p.1)) → ∀ t : Nat,
    callRun (w.map (fun p => (Vendor.R1.treeWeight p.1,p.2))) t =
      actualPrincipalWordRun w t := by
  induction w with
  | nil => intro _ t; rfl
  | cons p w ih =>
      intro hfinite t
      have heq := hfinite p (List.mem_cons_self)
      have hrepr : p.1.repr = (Vendor.R1.treeWeight p.1 : Ordinal) :=
        (congrArg ONote.repr heq).trans (ONote.repr_ofNat _)
      simp only [List.map_cons, callRun, actualPrincipalWordRun, hrepr]
      rw [ih (fun q hq => hfinite q (List.mem_cons_of_mem p hq))]

private theorem mapped_genuine (w : List (ONote × Nat)) :
    (∀ p ∈ w, p.1 = ONote.ofNat (Vendor.R1.treeWeight p.1)) → ∀ t : Nat,
    actualPrincipalWordGenuine w t →
      CallsGenuine (w.map (fun p => (Vendor.R1.treeWeight p.1,p.2))) t := by
  induction w with
  | nil => intro _ _ _; trivial
  | cons p w ih =>
      intro hfinite t hg
      have heq := hfinite p (List.mem_cons_self)
      have hrepr : p.1.repr = (Vendor.R1.treeWeight p.1 : Ordinal) :=
        (congrArg ONote.repr heq).trans (ONote.repr_ofNat _)
      have hfirst := hg.1
      rw [hrepr, finite_power_norm] at hfirst
      change p.2+Vendor.R1.treeWeight p.1+1 ≤ t ∧
        CallsGenuine (w.map (fun q => (Vendor.R1.treeWeight q.1,q.2)))
          (actualSuffixKernel (Ordinal.omega0 ^ (Vendor.R1.treeWeight p.1 : Ordinal)) p.2 t)
      refine ⟨by omega, ?_⟩
      apply ih (fun q hq => hfinite q (List.mem_cons_of_mem p hq))
      simpa only [hrepr] using hg.2

theorem headGraphExact : Targets.HeadGraphExact := by
  intro code hvalid
  obtain ⟨hnormal, hlimit, hpoly⟩ := hvalid
  let o : NONote := ⟨rawNoteDecode code,hnormal⟩
  let w := principalKernelWord (principalExponentBlocks o.1) 0
  have hencode : rawNoteEncode o.1 = code := rawNoteEncodeDecode code
  have hnorm : rawNormCode code = Vendor.R1.treeWeight o.1 :=
    (congrArg rawNormCode hencode).symm.trans (rawNormCodeCorrect o.1)
  have hcal : headCalls code = w.map (fun p => (Vendor.R1.treeWeight p.1,p.2)) :=
    (congrArg headCalls hencode).symm.trans (HeadProgramsProof.headCodeCalibration o.1).1
  have hdegree : headDegree code = 3+Vendor.R1.treeWeight o.1 := by
    rw [headDegree, hnorm]
  have hcalls := polynomialCalls o hlimit hpoly
  have hfinite : ∀ p ∈ w, p.1 = ONote.ofNat (Vendor.R1.treeWeight p.1) :=
    fun p hp => (hcalls p hp).2.1
  have hdegrees : ∀ p ∈ headCalls code, 1 ≤ p.1 ∧ p.1 ≤ headDegree code := by
    intro p hp
    rw [hcal] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hq' := hcalls q hq
    refine ⟨hq'.1, ?_⟩
    rw [hdegree]
    exact hq'.2.2.trans (by omega)
  have hcompiled := WordSemanticProof.callCompilationDegree (headDegree code) (headCalls code)
    (by rw [hdegree]; omega) hdegrees
  have hshiftAllowed : WordAllowed (headDegree code) [shiftLetter (rawNormCode code : Int)] := by
    intro a ha
    have heq : a = shiftLetter (rawNormCode code : Int) := List.mem_singleton.mp ha
    subst a
    simp [LetterAllowed, shiftLetter]
  refine ⟨prepend_allowed _ _ _ hshiftAllowed hcompiled, ?_⟩
  intro n
  have hp := fullActualPrincipalPeakWord o hlimit n
  have hg : CallsGenuine (headCalls code) (Vendor.R1.treeWeight o.1+n) := by
    rw [hcal]
    exact mapped_genuine w hfinite _ hp.2.2.1
  have hr : callRun (headCalls code) (Vendor.R1.treeWeight o.1+n) =
      actualPrincipalWordRun w (Vendor.R1.treeWeight o.1+n) := by
    rw [hcal]
    exact mapped_run w hfinite _
  have hcollapse : headValue code n =
      (callRun (headCalls code) (Vendor.R1.treeWeight o.1+n)).1 +
      (callRun (headCalls code) (Vendor.R1.treeWeight o.1+n)).2 := by
    change actualCollapse (o.1.repr+(n : Ordinal)) = _
    rw [hr]
    exact hp.2.2.2.2
  have hcomp := WordSemanticProof.callCompilationCorrect (headCalls code)
    (Vendor.R1.treeWeight o.1+n) (fun p hp => (hdegrees p hp).1) hg
  have hshiftValue : wordValue [shiftLetter (rawNormCode code : Int)] n =
      Vendor.R1.treeWeight o.1+n := by
    change ((n : Int)+(rawNormCode code : Int)).toNat = _
    rw [← Nat.cast_add, Int.toNat_natCast, hnorm, Nat.add_comm]
  have hshiftDomain : WordDomain [shiftLetter (rawNormCode code : Int)] n := by
    simpa [WordDomain, shiftLetter, LetterDomain] using
      add_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg (rawNormCode code))
  refine ⟨prepend_domain _ _ n hshiftDomain (by simpa only [hshiftValue] using hcomp.1), ?_⟩
  change unaryValue (prepend [shiftLetter (rawNormCode code : Int)]
    (compileCalls (headCalls code))) n = _
  rw [prepend_value, hshiftValue]
  simpa only [← hcollapse, Nat.cast_mul, Nat.cast_ofNat] using hcomp.2

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadSourceProof
