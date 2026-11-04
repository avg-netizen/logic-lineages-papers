module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.OmegaClosedProof
public import LogicLineages.OrdinalComparison.SourceSignedPairProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.OmegaSeed.Proof
open OriginalDomain FunctionalDetector.Proof SignedPair SignedPair.Proof

/-- Multiplication by a principal seed translates each Cantor exponent by
natural sum. The map retains integer coefficients, so common source heads
cancel before the constant pair is scaled. -/
noncomputable def seedShift (e : Ordinal) : CantorGroup →+ CantorGroup :=
  Finsupp.mapDomain.addMonoidHom (ordinalNaturalSum e)

private theorem principal_cnf_note (e : ONote) (c : ℕ+) :
    signedCNF (ONote.oadd e c .zero).repr = Finsupp.single e.repr ((c : Nat) : Int) := by
  ext x
  rw [cnf_apply,principal_actual_coefficient]
  by_cases he : e.repr=x
  · subst x
    simp only [Finsupp.single_eq_same,finite_nat]
  · simp [Finsupp.single_apply,he,Ne.symm he,finite_nat]

private theorem oadd_cnf (e : ONote) (c : ℕ+) (t : ONote)
    (ht : ONote.NF (.oadd e c t)) :
    signedCNF (ONote.oadd e c t).repr =
      Finsupp.single e.repr ((c : Nat) : Int)+signedCNF t.repr := by
  have hc : Ordinal.CNF.coeff Ordinal.omega0 (ONote.oadd e c t).repr =
      Finsupp.single e.repr ((c : Nat) : Ordinal)+Ordinal.CNF.coeff Ordinal.omega0 t.repr :=
    Ordinal.CNF.coeff_opow_mul_add Ordinal.one_lt_omega0
      (by exact_mod_cast c.ne_zero) (Ordinal.natCast_lt_omega0 _) ht.snd'.repr_lt
  ext x
  simp only [cnf_apply,hc,Finsupp.add_apply]
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite t.repr x)
  rw [hn]
  by_cases he : e.repr=x
  · subst x
    simp only [Finsupp.single_eq_same]
    rw [←Nat.cast_add,finite_nat ((c : Nat)+n),finite_nat n,Nat.cast_add]
  · simp [Finsupp.single_apply,he,Ne.symm he,finite_nat]

private theorem raw_sum_cnf (a b : ONote) (ha : ONote.NF a) (hb : ONote.NF b) :
    signedCNF (rawNaturalSum a b).repr = signedCNF a.repr+signedCNF b.repr := by
  have h := naturalSumDenotation (⟨a,ha⟩ : NONote) (⟨b,hb⟩ : NONote)
  change (rawNaturalSum a b).repr=ordinalNaturalSum a.repr b.repr at h
  rw [h,cnf_sum]

private theorem monomial_seed_cnf (e : ONote) (he : ONote.NF e) :
    ∀ t : ONote, ONote.NF t →
      signedCNF (rawMonomialProduct e 1 t).repr=seedShift e.repr (signedCNF t.repr)
  | .zero, _ => by
      have hz : signedCNF 0=0 := by simpa using cnf_nat 0
      simp [rawMonomialProduct,ONote.repr,hz]
  | .oadd f c t, ht => by
      rw [rawMonomialProduct,raw_sum_cnf]
      · rw [principal_cnf_note,monomial_seed_cnf e he t ht.snd,oadd_cnf f c t ht,
          map_add]
        have hf : (rawNaturalSum e f).repr=ordinalNaturalSum e.repr f.repr :=
          naturalSumDenotation (⟨e,he⟩ : NONote) (⟨f,ht.fst⟩ : NONote)
        simp only [hf,one_mul,seedShift,Finsupp.mapDomain.addMonoidHom_apply,
          Finsupp.mapDomain_single]
      · exact ONote.NF.oadd (rawNaturalSum_normal e f he ht.fst) _ ONote.NFBelow.zero
      · exact rawMonomialProduct_normal e he 1 t ht.snd

theorem principal_product_cnf (e : NONote) (a : Ordinal) (ha : a<epsilonZero) :
    signedCNF (ordinalNaturalProduct (Ordinal.omega0^e.1.repr) a) =
      seedShift e.1.repr (signedCNF a) := by
  obtain ⟨t,ht⟩ := normalRepresentationComplete a ha
  let p : NONote := ⟨.oadd e.1 1 .zero,ONote.NF.oadd e.2 1 ONote.NFBelow.zero⟩
  have hp : p.1.repr=Ordinal.omega0^e.1.repr := by simp [p,ONote.repr]
  rw [←ht,←hp,←naturalProductDenotation]
  have hprod : rawNaturalProduct p.1 t.1=rawMonomialProduct e.1 1 t.1 := by
    change rawNaturalSum (rawMonomialProduct e.1 1 t.1) .zero=_
    cases rawMonomialProduct e.1 1 t.1 <;> simp only [rawNaturalSum]
  change signedCNF (rawNaturalProduct p.1 t.1).repr=_
  rw [hprod]
  exact monomial_seed_cnf e.1 e.2 t.1 t.2

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.OmegaSeed.Proof
