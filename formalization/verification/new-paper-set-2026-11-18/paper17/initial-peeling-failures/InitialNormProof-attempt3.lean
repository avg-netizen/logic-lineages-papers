module
public import LogicLineages.PermittedControl.EqualRetainedReturnProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem raw_unit_weight_bound (a : ONote) (ha : ONote.NF a) :
    ∀ e ∈ (Ordinal.CNF Ordinal.omega0 a.repr).map Prod.fst,
      1+actualOrdinalNorm e ≤ Vendor.R1.treeWeight a := by
  induction a with
  | zero => simp [ONote.repr]
  | oadd b c t ihb iht =>
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd b c t).repr =
        (b.repr,((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
      Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc (Ordinal.natCast_lt_omega0 _) ha.snd'.repr_lt
    intro e he
    rw [hcnf,List.map_cons,List.mem_cons] at he
    change 1+actualOrdinalNorm e ≤ (c : Nat)*(1+Vendor.R1.treeWeight b)+Vendor.R1.treeWeight t
    rcases he with he | he
    · subst e
      rw [actualOrdinalNorm_notationCorrespondence (⟨b,ha.fst⟩ : NONote)]
      change 1+Vendor.R1.treeWeight b ≤ (c : Nat)*(1+Vendor.R1.treeWeight b)+Vendor.R1.treeWeight t
      have h := Nat.le_mul_of_pos_left (1+Vendor.R1.treeWeight b) c.pos
      omega
    · exact (iht ha.snd e he).trans (Nat.le_add_left _ _)

 theorem initial_unit_weight_bound (mu : Ordinal.{0}) (hmu : mu < epsilonZero)
    (e : Ordinal.{0}) (he : e ∈ (Ordinal.CNF Ordinal.omega0 mu).map Prod.fst) :
    e < epsilonZero ∧ 1+actualOrdinalNorm e ≤ actualOrdinalNorm mu := by
  have hb : e < epsilonZero := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    exact (cnfDescentBelowEpsilonZero mu hmu p hp).1.trans hmu
  obtain ⟨a,rfl⟩ := normalRepresentationComplete mu hmu
  refine ⟨hb,?_⟩
  rw [actualOrdinalNorm_notationCorrespondence a]
  exact raw_unit_weight_bound a.1 a.2 e he


 theorem initial_leading_norm (delta : Ordinal.{0}) (hd : delta < epsilonZero)
    (hpos : delta ≠ 0) :
    Ordinal.log Ordinal.omega0 delta < epsilonZero ∧
    actualOrdinalNorm (Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) ≤ actualOrdinalNorm delta := by
  have hm : Ordinal.log Ordinal.omega0 delta ∈ (Ordinal.CNF Ordinal.omega0 delta).map Prod.fst := by
    rw [Ordinal.CNF.ne_zero hpos]
    simp
  have h := initial_unit_weight_bound delta hd _ hm
  refine ⟨h.1,?_⟩
  have hn := thick_monomial_norm _ h.1 1
  simpa using hn.le.trans h.2

end LogicLineages.PermittedControl
