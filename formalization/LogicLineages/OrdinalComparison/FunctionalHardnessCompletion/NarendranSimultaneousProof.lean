module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.NarendranConstantProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran.Proof
open Polynomial

private theorem enough_twos (n : Nat) : n+1 ≤ (2 : Nat)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

theorem exactSimultaneousConstants : Targets.ExactSimultaneousConstants := by
  intro n z
  constructor
  · rintro ⟨v,extra,w,hg,hsum⟩
    obtain ⟨k,hv⟩ := (exactConstantGadget v).mp ⟨w,hg⟩
    intro i
    refine ⟨(z i).coeff 0, ?_⟩
    ext j
    by_cases hj : j=0
    · subst j
      simp
    · have he := congrArg (fun p : NPolynomial => p.coeff j) hsum
      rw [hv] at he
      simp only [Polynomial.coeff_add,Polynomial.finsetSum_coeff,
        Polynomial.coeff_C,if_neg hj] at he
      have hle : (z i).coeff j ≤ ∑ t : Fin n, (z t).coeff j :=
        Finset.single_le_sum (f:=fun t : Fin n => (z t).coeff j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hzero : (z i).coeff j = 0 := by omega
      simpa only [Polynomial.coeff_C,if_neg hj] using hzero
  · intro hz
    classical
    let a : Fin n → Nat := fun i => Classical.choose (hz i)
    have ha : ∀ i, z i = C (a i) := fun i => Classical.choose_spec (hz i)
    let s : Nat := ∑ i : Fin n, a i
    let m : Nat := 2^s-1
    have hbound : s ≤ m := by
      have h := enough_twos s
      omega
    have hsum : (∑ i : Fin n, z i) = C s := by
      simp only [ha]
      rw [← map_sum]
    obtain ⟨w,hw⟩ := (exactConstantGadget (C m)).mpr ⟨s,rfl⟩
    refine ⟨C m,C (m-s),w,hw,?_⟩
    rw [hsum,←Polynomial.C_add]
    have he : s+(m-s)=m := by omega
    rw [he]

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran.Proof
