module
public import LogicLineages.OrdinalComparison.PaidHeadTransportTargets
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.PaidHeadTransport.Proof
open SignedPair SignedPair.Proof FunctionalDetector.Proof

private theorem signed_injective : Function.Injective signedCNF := by
  intro a b he
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  have hei := congrArg (fun f : CantorGroup => f e) he
  simp only [cnf_apply] at hei
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite b e)
  rw [hm,hn,finite_nat,finite_nat] at hei
  have hmn : m=n := by exact_mod_cast hei
  rw [hm,hn,hmn]

private theorem omega_nat_coeff (n : Nat) :
    Ordinal.CNF.coeff Ordinal.omega0 (Ordinal.omega0*(n:Ordinal)) =
      Finsupp.single 1 (n:Ordinal) := by
  by_cases hn : n=0
  · subst n; simp
  · simpa only [Ordinal.opow_one, add_zero, Ordinal.CNF.coeff_zero_right, add_zero] using
      Ordinal.CNF.coeff_opow_mul_add (e:=1) (y:=0) Ordinal.one_lt_omega0
        (by exact_mod_cast hn) (Ordinal.natCast_lt_omega0 n) (by simp)

private theorem omega_nat_signed (n : Nat) :
    signedCNF (Ordinal.omega0*(n:Ordinal)) = Finsupp.single 1 (n:Int) := by
  unfold signedCNF
  rw [omega_nat_coeff, Finsupp.mapRange_single]
  simp only [finite_nat]

private theorem omega_product_zero_coeff (a : Ordinal) (ha : a<epsilonZero) :
    Ordinal.CNF.coeff Ordinal.omega0 (ordinalNaturalProduct Ordinal.omega0 a) 0=0 := by
  have hz : signedCNF (ordinalNaturalProduct Ordinal.omega0 a) 0=0 := by
    rw [cnf_omega_product a ha]
    exact Finsupp.mapDomain_notin_range (signedCNF a) 0 (by
      rintro ⟨e, he⟩
      change e+1=0 at he
      have h : e < e+1 := lt_add_one e
      rw [he] at h
      exact (not_lt_of_ge (show (0:Ordinal) ≤ e from zero_le)) h)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite (ordinalNaturalProduct Ordinal.omega0 a) 0)
  rw [cnf_apply, hn, finite_nat] at hz
  have hn0 : n=0 := by exact_mod_cast hz
  rw [hn,hn0,Nat.cast_zero]

theorem exactOmegaFiniteTail : Targets.ExactOmegaFiniteTail := by
  intro a ha δ
  have hδ : (δ:Ordinal)<epsilonZero := by
    have h := normalRepresentationSound (NONote.ofNat δ)
    change (ONote.ofNat δ).repr < epsilonZero at h
    simpa only [ONote.repr_ofNat] using h
  have htail : a+(δ:Ordinal)<epsilonZero := by
    rw [← actualNaturalSumFiniteRight]
    exact sum_below_epsilon a _ ha hδ
  have hsum : ordinalNaturalProduct Ordinal.omega0 (a+(δ:Ordinal)) =
      ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) (Ordinal.omega0*(δ:Ordinal)) := by
    apply signed_injective
    rw [cnf_omega_product _ htail, ← actualNaturalSumFiniteRight a δ, cnf_sum,
      shift_add, cnf_nat, cnf_sum, cnf_omega_product _ ha, omega_nat_signed]
    simp only [omegaShift,Finsupp.mapDomain_single,zero_add]
  rw [hsum]
  unfold ordinalNaturalSum
  rw [omega_nat_coeff, Ordinal.CNF.eval_add]
  · rw [Ordinal.CNF.eval_coeff, Ordinal.CNF.eval_single, Ordinal.opow_one]
  · intro e he d hd
    have hd1 : d=1 := by
      by_contra h
      simpa [Finsupp.mem_support_iff,Finsupp.single_apply,h,Ne.symm h] using hd
    subst d
    have he0 : e≠0 := by
      intro h
      subst e
      exact (Finsupp.mem_support_iff.mp he) (omega_product_zero_coeff a ha)
    exact (Order.one_le_iff_ne_zero).mpr he0
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.PaidHeadTransport.Proof
