module
public import LogicLineages.OrdinalComparison.SourceSignedPairTargets
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorHeadOrderProof
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Finsupp.SMul
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SignedPair.Proof
open OriginalDomain FunctionalDetector.Proof

@[simp] theorem finite_nat (n : Nat) : finiteValue (n:Ordinal)=n := originalFiniteValueCalibration n

@[simp] theorem finite_zero : finiteValue 0=0 := by simpa only [Nat.cast_zero] using finite_nat 0

@[simp] theorem cnf_apply (a e : Ordinal) : signedCNF a e = (finiteValue (Ordinal.CNF.coeff Ordinal.omega0 a e) : Int) := rfl

theorem cnf_sum (a b : Ordinal) : signedCNF (ordinalNaturalSum a b)=signedCNF a+signedCNF b := by
  ext e
  simp only [cnf_apply,sum_coeff,Finsupp.add_apply]
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite b e)
  rw [hm,hn,← Nat.cast_add,finite_nat (m+n),finite_nat m,finite_nat n,Nat.cast_add]

theorem cnf_nat (n : Nat) : signedCNF (n : Ordinal)=Finsupp.single 0 (n : Int) := by
  have hc : Ordinal.CNF.coeff Ordinal.omega0 (n : Ordinal)=Finsupp.single 0 (n : Ordinal) := by
    by_cases hn : n=0
    · subst n; simp
    · simpa only [Ordinal.opow_zero,one_mul,add_zero,Ordinal.CNF.coeff_zero_right] using
        Ordinal.CNF.coeff_opow_mul_add (e:=0) (y:=0) Ordinal.one_lt_omega0
          (by exact_mod_cast hn) (Ordinal.natCast_lt_omega0 n) (by simp)
  ext e
  rw [cnf_apply,hc]
  by_cases he : 0=e
  · subst e; simp only [Finsupp.single_eq_same,finite_nat]
  · simp [Finsupp.single_apply,he,Ne.symm he,finite_nat]

theorem cnf_finite_product (c : ℕ+) (a : Ordinal) (ha : a<epsilonZero) :
    signedCNF (ordinalNaturalProduct ((c:Nat):Ordinal) a)=((c:Nat):Int) • signedCNF a := by
  ext e
  simp only [cnf_apply,Finsupp.smul_apply,smul_eq_mul]
  rw [finite_product_coeff c a ha e]
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
  rw [hn,← Ordinal.natCast_mul]
  simp only [finite_nat,Nat.cast_mul]

theorem shift_add (a b : CantorGroup) : omegaShift (a+b)=omegaShift a+omegaShift b :=
  Finsupp.mapDomain_add
 theorem shift_sub (a b : CantorGroup) : omegaShift (a-b)=omegaShift a-omegaShift b :=
  Finsupp.mapDomain_sub
 theorem shift_smul (k : Int) (a : CantorGroup) : omegaShift (k • a)=k • omegaShift a :=
  (Finsupp.mapDomain.addMonoidHom (fun e : Ordinal => e+1)).map_zsmul k a

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

private theorem monomial_shift_cnf : ∀ t : ONote, ONote.NF t →
    signedCNF (rawMonomialProduct 1 1 t).repr=omegaShift (signedCNF t.repr)
  | .zero, _ => by
      have hz : signedCNF 0=0 := by simpa using cnf_nat 0
      simp [rawMonomialProduct,ONote.repr,hz,omegaShift]
  | .oadd e c t, ht => by
    rw [rawMonomialProduct,cnf_raw_sum]
    · rw [cnf_principal,monomial_shift_cnf t ht.snd,cnf_oadd e c t ht,shift_add]
      have he : (rawNaturalSum 1 e).repr=e.repr+1 := by
        have hd := naturalSumDenotation (⟨1,ONote.nf_one⟩ : NONote) (⟨e,ht.fst⟩ : NONote)
        change (rawNaturalSum 1 e).repr=ordinalNaturalSum (1:ONote).repr e.repr at hd
        rw [hd,ONote.repr_one,sum_comm]
        simpa using actualNaturalSumFiniteRight e.repr 1
      simp only [he,one_mul,omegaShift,Finsupp.mapDomain_single]
    · exact ONote.NF.oadd (rawNaturalSum_normal 1 e ONote.nf_one ht.fst) _ ONote.NFBelow.zero
    · exact rawMonomialProduct_normal 1 ONote.nf_one 1 t ht.snd

theorem cnf_omega_product (a : Ordinal) (ha : a<epsilonZero) :
    signedCNF (ordinalNaturalProduct Ordinal.omega0 a)=omegaShift (signedCNF a) := by
  obtain ⟨t,ht⟩ := normalRepresentationComplete a ha
  let w : NONote := ⟨.oadd 1 1 .zero,ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  have hw : w.1.repr=Ordinal.omega0 := by simp [w,ONote.repr]
  rw [← ht,← hw,← naturalProductDenotation]
  have hp : rawNaturalProduct w.1 t.1=rawMonomialProduct 1 1 t.1 := by
    change rawNaturalSum (rawMonomialProduct 1 1 t.1) .zero=_
    cases rawMonomialProduct 1 1 t.1 <;> simp only [rawNaturalSum]
  change signedCNF (rawNaturalProduct w.1 t.1).repr=_
  rw [hp]
  exact monomial_shift_cnf t.1 t.2
end LogicLineages.OrdinalComparison.Source.SignedPair.Proof
