module
public import LogicLineages.PermittedControl.SelectedOmegaClosedProof
public import LogicLineages.PermittedControl.SelectedHardnessSignedProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
open OrdinalComparison Source Source.SignedPair Source.SignedPair.Proof
open Source.FunctionalDetector.Proof
open Vendor.R1

private theorem cnf_principal (e : ONote) (c : ℕ+) :
    signedCNF (ONote.oadd e c .zero).repr=Finsupp.single e.repr ((c:Nat):Int) := by
  ext x
  rw [cnf_apply,principal_actual_coefficient]
  by_cases he : e.repr=x
  · subst x; simp only [Finsupp.single_eq_same,finite_nat]
  · simp [Finsupp.single_apply,he,Ne.symm he,finite_nat]

private theorem cnf_oadd (e : ONote) (c : ℕ+) (t : ONote) (ht : ONote.NF (.oadd e c t)) :
    signedCNF (ONote.oadd e c t).repr=Finsupp.single e.repr ((c:Nat):Int)+signedCNF t.repr := by
  have hc : Ordinal.CNF.coeff Ordinal.omega0 (ONote.oadd e c t).repr=
      Finsupp.single e.repr ((c:Nat):Ordinal)+Ordinal.CNF.coeff Ordinal.omega0 t.repr :=
    Ordinal.CNF.coeff_opow_mul_add Ordinal.one_lt_omega0
      (by exact_mod_cast c.ne_zero) (Ordinal.natCast_lt_omega0 _) ht.snd'.repr_lt
  ext x
  simp only [cnf_apply,hc,Finsupp.add_apply]
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite t.repr x)
  rw [hn]
  by_cases he : e.repr=x
  · subst x
    simp only [Finsupp.single_eq_same]
    rw [← Nat.cast_add,finite_nat ((c:Nat)+n),finite_nat n,Nat.cast_add]
  · simp [Finsupp.single_apply,he,Ne.symm he,finite_nat]

private theorem cnf_raw_sum (a b : ONote) (ha : ONote.NF a) (hb : ONote.NF b) :
    signedCNF (rawNaturalSum a b).repr=signedCNF a.repr+signedCNF b.repr := by
  have h := naturalSumDenotation (⟨a,ha⟩ : NONote) (⟨b,hb⟩ : NONote)
  change (rawNaturalSum a b).repr=ordinalNaturalSum a.repr b.repr at h
  rw [h,cnf_sum]

private theorem monomial_shift_cnf (k : ℕ+) : ∀ t : ONote, ONote.NF t →
    signedCNF (rawMonomialProduct 1 k t).repr=((k : Nat) : Int) • omegaShift (signedCNF t.repr)
  | .zero, _ => by
      have hz : signedCNF 0=0 := by simpa using cnf_nat 0
      simp [rawMonomialProduct,ONote.repr,hz,omegaShift]
  | .oadd e c t, ht => by
    rw [rawMonomialProduct,cnf_raw_sum]
    · rw [cnf_principal,monomial_shift_cnf k t ht.snd,cnf_oadd e c t ht,shift_add,smul_add]
      have he : (rawNaturalSum 1 e).repr=e.repr+1 := by
        have hd := naturalSumDenotation (⟨1,ONote.nf_one⟩ : NONote) (⟨e,ht.fst⟩ : NONote)
        change (rawNaturalSum 1 e).repr=ordinalNaturalSum (1:ONote).repr e.repr at hd
        rw [hd,ONote.repr_one,sum_comm]
        simpa using actualNaturalSumFiniteRight e.repr 1
      simp [he,omegaShift,Finsupp.mapDomain_single,Finsupp.smul_single,PNat.mul_coe,Nat.cast_mul]
    · exact ONote.NF.oadd (rawNaturalSum_normal 1 e ONote.nf_one ht.fst) _ ONote.NFBelow.zero
    · exact rawMonomialProduct_normal 1 ONote.nf_one k t ht.snd

theorem two_omega_product_cnf (a : Ordinal) (ha : a<epsilonZero) :
    signedCNF (ordinalNaturalProduct (ordinalNaturalProduct 2 Ordinal.omega0) a)=
      (2 : Int) • omegaShift (signedCNF a) := by
  obtain ⟨t,ht⟩ := normalRepresentationComplete a ha
  let w : NONote := ⟨.oadd 1 2 .zero,ONote.NF.oadd ONote.nf_one 2 ONote.NFBelow.zero⟩
  let two : NONote := ⟨ONote.ofNat 2,by infer_instance⟩
  let om : NONote := ⟨ONote.omega,by decide⟩
  have hw : w.1.repr=ordinalNaturalProduct 2 Ordinal.omega0 := by
    have h := naturalProductDenotation two om
    have hn : (naturalProduct two om).1=w.1 := by decide +kernel
    rw [hn] at h
    simpa [two,om,ONote.omega,ONote.repr] using h
  rw [←ht,←hw,←naturalProductDenotation]
  have hp : rawNaturalProduct w.1 t.1=rawMonomialProduct 1 2 t.1 := by
    change rawNaturalSum (rawMonomialProduct 1 2 t.1) .zero=_
    cases rawMonomialProduct 1 2 t.1 <;> simp only [rawNaturalSum]
  change signedCNF (rawNaturalProduct w.1 t.1).repr=_
  rw [hp]
  simpa using monomial_shift_cnf 2 t.1 t.2

private theorem signed_injective : Function.Injective signedCNF := by
  intro a b hab
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite b e)
  have he := congrArg (fun g : CantorGroup => g e) hab
  simp only [cnf_apply,hm,hn,finite_nat] at he
  have hmn : m=n := by exact_mod_cast he
  rw [hm,hn,hmn]

 theorem higher_value (a : Ordinal) (ha : a<epsilonZero) :
    ordinalNaturalProduct ((2 : Ordinal)^Ordinal.omega0)
      (ordinalNaturalSum 1 (ordinalNaturalSum a a))=
    ordinalNaturalSum Ordinal.omega0
      (ordinalNaturalProduct (ordinalNaturalProduct 2 Ordinal.omega0) a) := by
  have hp : (2 : Ordinal)^Ordinal.omega0=Ordinal.omega0 := by
    simpa using Ordinal.natCast_opow_omega0 (by decide : 1<(2 : Nat))
  have h1 : (1 : Ordinal)<epsilonZero := SelectedValueClosureProof.closed_below (fun n => n) .one
  have hb := sum_below_epsilon _ _ h1 (sum_below_epsilon _ _ ha ha)
  apply signed_injective
  rw [hp,cnf_omega_product _ hb,cnf_sum,cnf_sum,shift_add,shift_add,
    cnf_sum,two_omega_product_cnf a ha]
  have hs : omegaShift (signedCNF 1)=signedCNF Ordinal.omega0 := by
    have ho := FunctionalHardnessCompletion.OmegaSeed.Proof.principal_cnf (1 : Ordinal)
    rw [Ordinal.opow_one] at ho
    rw [ho]
    simp [omegaShift,show signedCNF (1 : Ordinal)=Finsupp.single 0 (1 : Int) by
      simpa only [Nat.cast_one] using cnf_nat 1]
  rw [hs]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

end LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
