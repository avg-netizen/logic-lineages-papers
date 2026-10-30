module
public import LogicLineages.OrdinalComparison.RepeatedWordOrderTargets
public import LogicLineages.OrdinalComparison.RepeatedPrincipalWordProof
public import LogicLineages.OrdinalComparison.SuffixKernelMonotoneProof
public import LogicLineages.OrdinalComparison.SmallKernelsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem repeated_word_cons (eta : NONote) (he : 0 < eta.1.repr) (q c : Nat) :
    principalKernelWord (List.replicate (q+1) eta.1) c =
      (eta.1, c+q*actualOrdinalNorm (Ordinal.omega0^eta.1.repr)) ::
        principalKernelWord (List.replicate q eta.1) c := by
  rw [actualRepeatedPrincipalWordPositions eta he, actualRepeatedPrincipalWordPositions eta he]
  simp [List.range_succ, List.reverse_append]

private theorem repeated_word_run_succ (eta : NONote) (he : 0 < eta.1.repr) (q c t : Nat) :
    (actualPrincipalWordRun (principalKernelWord (List.replicate (q+1) eta.1) c) t).1 =
      (actualPrincipalWordRun (principalKernelWord (List.replicate q eta.1) c)
        (actualSuffixKernel (Ordinal.omega0^eta.1.repr)
          (c+q*actualOrdinalNorm (Ordinal.omega0^eta.1.repr)) t)).1 := by
  rw [repeated_word_cons eta he]
  rfl

private theorem kernel_ge_input (theta : Ordinal) (a t : Nat) :
    t ≤ actualSuffixKernel theta a t := by
  have h := iterate_index_mono (fun n => (self_lt_Phi n).le) t
    (Nat.zero_le (actualSuffixKernelCount theta a t))
  change t ≤ (Phi^[actualSuffixKernelCount theta a t]) t
  simpa only [Function.iterate_zero_apply] using h

theorem actualRepeatedWordWeakOrder : Targets.ActualRepeatedWordWeakOrder := by
  intro eta he q
  have heps : Ordinal.omega0^eta.1.repr < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr (normalRepresentationSound eta)
  induction q with
  | zero => intro c e U V hce hU hUV; exact hUV
  | succ q ih =>
    intro c e U V hce hU hUV
    rw [repeated_word_run_succ eta he q e, repeated_word_run_succ eta he q c]
    let w := actualOrdinalNorm (Ordinal.omega0^eta.1.repr)
    have hdom : e+q*w+w ≤ U := by simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hU
    have hdom' : c+q*w+w ≤ V := by omega
    apply ih c e _ _ hce
    · exact (by omega : e+q*w ≤ U).trans (kernel_ge_input _ _ _)
    · exact actualSuffixKernelInputMassMonotone eta.1.repr he heps _ _ U V (by omega) hUV hdom hdom'

theorem actualRepeatedWordStrictInput : Targets.ActualRepeatedWordStrictInput := by
  intro eta he q
  have heps : Ordinal.omega0^eta.1.repr < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr (normalRepresentationSound eta)
  induction q with
  | zero => intro c e U V hce hU hUV; exact hUV
  | succ q ih =>
    intro c e U V hce hU hUV
    rw [repeated_word_run_succ eta he q e, repeated_word_run_succ eta he q c]
    let w := actualOrdinalNorm (Ordinal.omega0^eta.1.repr)
    have hdom : e+q*w+w ≤ U := by simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hU
    have hdom' : c+q*w+w ≤ V := by omega
    apply ih c e _ _ hce
    · exact (by omega : e+q*w ≤ U).trans (kernel_ge_input _ _ _)
    · exact actualSuffixKernelStrictInput eta.1.repr he heps _ _ U V (by omega) hUV hdom hdom'

theorem actualRepeatedWordStrictMass : Targets.ActualRepeatedWordStrictMass := by
  intro eta he S hcase q c e U V hq hce hSU hU hUV
  by_cases hlt : U < V
  · exact actualRepeatedWordStrictInput eta he q c e U V hce.le hU hlt
  have hVU : V=U := by omega
  subst V
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hq
  have heps : Ordinal.omega0^eta.1.repr < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr (normalRepresentationSound eta)
  let theta := Ordinal.omega0^eta.1.repr
  let w := actualOrdinalNorm theta
  have hqform : 2+j=(j+1)+1 := by omega
  rw [hqform] at hU ⊢
  rw [repeated_word_run_succ eta he (j+1) e, repeated_word_run_succ eta he (j+1) c]
  let a := c+(j+1)*w
  let b := e+(j+1)*w
  let lo := actualSuffixKernel theta b U
  let hi := actualSuffixKernel theta a U
  have hab : a < b := by dsimp [a,b]; omega
  have hbU : b+w ≤ U := by
    simpa only [b, w, theta, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hU
  have haU : a+w ≤ U := by omega
  have hweak : lo ≤ hi := actualSuffixKernelInputMassMonotone eta.1.repr he heps a b U U hab.le le_rfl hbU haU
  have hUlo : U ≤ lo := kernel_ge_input _ _ _
  have hnext : e+(j+1)*w ≤ lo := by omega
  by_cases hstrict : lo < hi
  · exact actualRepeatedWordStrictInput eta he (j+1) c e lo hi hce.le hnext hstrict
  have hequal : lo=hi := by omega
  rcases hcase with ⟨htheta, hS⟩ | ⟨_, hIH⟩
  · have hw : w=3 := by
      change actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=3
      rw [htheta]
      simpa only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.mul_one] using
        (actualFiniteMonomialFacts 2 1).2.1
    have hceil : (b+1)/2=(a+1)/2 := by
      have hh := (actualOmegaSquaredMassClasses b a U (by omega) (by omega)).1
      apply hh.mp
      simpa only [lo, hi, theta, htheta] using hequal
    have hceilnext : (c+j*w+1)/2 < (e+j*w+1)/2 := by
      dsimp [a,b] at hab hceil
      rw [hw] at hceil ⊢
      omega
    have hnextE : e+j*w+3 ≤ lo := by
      have hh := hnext
      rw [hw] at hh ⊢
      omega
    have hnextC : c+j*w+3 ≤ lo := by omega
    have hsecond : actualSuffixKernel theta (e+j*w) lo < actualSuffixKernel theta (c+j*w) hi := by
      rw [← hequal]
      change actualSuffixKernel (Ordinal.omega0^eta.1.repr) (e+j*w) lo < _
      simp only [theta, htheta]
      exact (actualOmegaSquaredMassClasses (e+j*w) (c+j*w) lo hnextE hnextC).2.mpr hceilnext
    rw [repeated_word_run_succ eta he j e, repeated_word_run_succ eta he j c]
    apply actualRepeatedWordStrictInput eta he j c e _ _ hce.le
    · exact (by omega : e+j*w ≤ lo).trans (kernel_ge_input _ _ _)
    · exact hsecond
  · have hs : lo < hi := hIH U a b hSU hab hbU
    omega

end LogicLineages.OrdinalComparison
