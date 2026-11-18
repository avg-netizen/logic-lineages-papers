module
public import LogicLineages.PermittedControl.HighestPieceTargets
public import LogicLineages.PermittedControl.FiniteProfileProof
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem raw_exponent_bound (a : ONote) (ha : ONote.NF a) :
    ∀ e ∈ (Ordinal.CNF Ordinal.omega0 a.repr).map Prod.fst,
      actualOrdinalNorm e ≤ Vendor.R1.treeWeight a := by
  induction a with
  | zero => simp [ONote.repr]
  | oadd b c t ihb iht =>
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd b c t).repr =
        (b.repr,((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
      Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc (Ordinal.natCast_lt_omega0 _) ha.snd'.repr_lt
    intro e he
    rw [hcnf,List.map_cons,List.mem_cons] at he
    change actualOrdinalNorm e ≤ (c : Nat)*(1+Vendor.R1.treeWeight b)+Vendor.R1.treeWeight t
    rcases he with he | he
    · subst e
      rw [actualOrdinalNorm_notationCorrespondence (⟨b,ha.fst⟩ : NONote)]
      change Vendor.R1.treeWeight b ≤ (c : Nat)*(1+Vendor.R1.treeWeight b)+Vendor.R1.treeWeight t
      have h := Nat.le_mul_of_pos_left (1+Vendor.R1.treeWeight b) c.pos
      omega
    · exact (iht ha.snd e he).trans (Nat.le_add_left _ _)

 theorem actual_profile_breakpoint_bound (mu : Ordinal.{0}) (hmu : mu < epsilonZero)
    (e : Ordinal.{0}) (he : e ∈ (Ordinal.CNF Ordinal.omega0 mu).map Prod.fst) :
    e < epsilonZero ∧ actualOrdinalNorm e ≤ actualOrdinalNorm mu := by
  have hb : e < epsilonZero := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    exact (cnfDescentBelowEpsilonZero mu hmu p hp).1.trans hmu
  obtain ⟨a,rfl⟩ := normalRepresentationComplete mu hmu
  refine ⟨hb,?_⟩
  rw [actualOrdinalNorm_notationCorrespondence a]
  exact raw_exponent_bound a.1 a.2 e he

 theorem jointProfileCoverBound : Targets.JointProfileCoverBound := by
  intro mu nu E hmu hnu hE y hy
  have hy' := List.mem_filter.mp hy
  have hyE : y < E := (of_decide_eq_true hy'.2).2
  refine ⟨hyE.trans hE,?_⟩
  have hb : ∀ b ∈ jointProfileBreakpoints mu nu,
      b < epsilonZero ∧ actualOrdinalNorm b ≤ actualOrdinalNorm mu+actualOrdinalNorm nu := by
    intro b hb
    rcases List.mem_append.mp hb with hm | hn
    · have h := actual_profile_breakpoint_bound mu hmu b hm
      exact ⟨h.1,h.2.trans (Nat.le_add_right _ _)⟩
    · have h := actual_profile_breakpoint_bound nu hnu b hn
      exact ⟨h.1,h.2.trans (Nat.le_add_left _ _)⟩
  rcases List.mem_cons.mp hy'.1 with hz | hm
  · subst y
    have hn : actualOrdinalNorm (2 : Ordinal.{0})=2 := by
      have h := actualOrdinalNorm_notationCorrespondence (NONote.ofNat 2)
      change actualOrdinalNorm (ONote.ofNat 2).repr = 2 at h
      simpa using h
    rw [hn]
    omega
  · rcases List.mem_append.mp hm with hm | hm
    · exact (hb y hm).2.trans (by omega)
    · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp hm
      have h := hb b hbmem
      have hn : actualOrdinalNorm (b+1)=actualOrdinalNorm b+1 := by
        simpa using (actualFiniteTailClosureNorm b h.1 1).2
      rw [hn]
      omega

 theorem jointProfilePieceOrder : Targets.JointProfilePieceOrder := by
  intro mu nu x y z hyx hne hxz
  by_contra hyz
  have hzy : z ≤ y := le_of_not_gt hyz
  apply hne
  intro b hb
  constructor
  · exact fun h => hyx.le.trans h
  · intro hyb
    exact (hxz b hb).mpr (hzy.trans hyb)

end LogicLineages.PermittedControl
