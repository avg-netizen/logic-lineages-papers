module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorTargets
public import LogicLineages.OrdinalComparison.WWAdmissibleSumProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof

theorem coeff_finite (a e : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 a e < Ordinal.omega0 := by
  by_cases he : e ∈ (Ordinal.CNF Ordinal.omega0 a).map Prod.fst
  · obtain ⟨⟨e,c⟩,hm,rfl⟩ := List.mem_map.mp he
    rw [Ordinal.CNF.coeff_of_mem_CNF hm]
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hm
  · rw [Ordinal.CNF.coeff_of_notMem_CNF he]
    exact Ordinal.omega0_pos

theorem sum_coeff (a b : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 (ordinalNaturalSum a b)=
      Ordinal.CNF.coeff Ordinal.omega0 a+Ordinal.CNF.coeff Ordinal.omega0 b := by
  apply Ordinal.CNF.coeff_eval Ordinal.one_lt_omega0
  intro e
  exact Ordinal.isPrincipal_add_omega0 (coeff_finite a e) (coeff_finite b e)

theorem sum_comm (a b : Ordinal) : ordinalNaturalSum a b=ordinalNaturalSum b a := by
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  rw [sum_coeff,sum_coeff]
  ext e
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite b e)
  simp only [Finsupp.add_apply,hm,hn]
  exact_mod_cast Nat.add_comm m n

theorem sum_assoc (a b c : Ordinal) :
    ordinalNaturalSum (ordinalNaturalSum a b) c=ordinalNaturalSum a (ordinalNaturalSum b c) := by
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  simp only [sum_coeff,add_assoc]

noncomputable def paddedHead (a : Ordinal) : Ordinal :=
  ordinalNaturalSum (ordinalNaturalSum 1 (ordinalNaturalSum a 1)) a

theorem paddedHead_injective : Function.Injective paddedHead := by
  intro a b h
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  have he := congrArg (fun x => Ordinal.CNF.coeff Ordinal.omega0 x e) h
  simp only [paddedHead,sum_coeff,Finsupp.add_apply] at he
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite b e)
  obtain ⟨k,hk⟩ := Ordinal.lt_omega0.mp (coeff_finite 1 e)
  rw [hm,hn,hk] at he
  have hh : k+(m+k)+m=k+(n+k)+n := by exact_mod_cast he
  have hh' : m=n := by omega
  rw [hm,hn,hh']
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
