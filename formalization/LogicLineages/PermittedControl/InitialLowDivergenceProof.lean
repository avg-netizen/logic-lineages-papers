module
public import LogicLineages.PermittedControl.InitialLowClassificationProof
public import LogicLineages.PermittedControl.InitialHighDivergenceProof
public import LogicLineages.PermittedControl.DoubleQuadraticDivergenceProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem quadratic_prefix_log (L : Ordinal.{0}) (k : Nat) (hLpos : 0 < L)
    (hd : Ordinal.omega0^(2 : Ordinal) ∣ L) :
    Ordinal.log Ordinal.omega0 (thickBlock L 2 k)=Ordinal.log Ordinal.omega0 L := by
  by_cases hk : k=0
  · simp [hk,thickBlock]
  · simpa only [if_neg hLpos.ne'] using thick_block_leading L 2 k (Nat.pos_of_ne_zero hk) hd

 theorem initial_low_divergence (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu delta A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hd : delta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hdl : Order.IsSuccLimit delta)
    (ht : thickBlockTail (initialPeelingRadius mu nu delta) B ≤ t)
    (hpart : actualLimitPart A=mu+delta) (hpart' : actualLimitPart A'=nu+delta)
    (hN : actualOrdinalNorm A=t) (hN' : actualOrdinalNorm A'=t)
    (hc : relativeProfile mu (Ordinal.log Ordinal.omega0 delta)<relativeProfile nu (Ordinal.log Ordinal.omega0 delta))
    (hlow : ∀ e ∈ initialPeelingUnits delta, e ≤ 2)
    (hfail : ¬ initialPeelingPass mu nu delta) :
    Targets.OrientedUnitDivergence f mu nu (Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) A A' := by
  obtain ⟨q,n,hunits,hshape⟩ := initial_at_most_quadratic_units delta hd hdl hlow
  have hq : 0 < q := by
    by_contra hh
    have hq0 : q=0 := by omega
    apply hfail
    right; left
    intro e he
    simp only [initialPeelingUnits,hunits,List.tail_cons,hq0,List.replicate_zero,List.nil_append,List.mem_reverse] at he
    have he1 := (List.mem_replicate.mp he).2
    rw [he1]
    norm_num
  let E := Ordinal.log Ordinal.omega0 delta
  let L := Ordinal.omega0^E
  let R := initialPeelingRadius mu nu delta
  have hE2 : (2 : Ordinal) ≤ E := by
    have ho := original_units_order delta hd
    rw [hunits,List.pairwise_cons] at ho
    exact ho.1 2 (List.mem_append_left _ (List.mem_replicate.mpr ⟨hq.ne',rfl⟩))
  have hlead := initial_leading_norm delta hd hdl.bot_lt.ne'
  have hL : L < epsilonZero := phase_power_below E hlead.1
  have hLpos : 0 < L := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hLd : Ordinal.omega0^(2 : Ordinal) ∣ L := Ordinal.opow_dvd_opow Ordinal.omega0 hE2
  have hlogL : Ordinal.log Ordinal.omega0 L=E := Ordinal.log_opow Ordinal.one_lt_omega0 E
  have ha : (2 : Ordinal.{0}) < epsilonZero := by simpa using finiteCoefficient_below 0 2
  let P := thickBlock L 2 (q-1)
  have hP : P < epsilonZero := thick_block_below L 2 (q-1) hL ha
  have hPpos : 0 < P := hLpos.trans_le le_self_add
  have hPd : Ordinal.omega0^(2 : Ordinal) ∣ P := thick_block_divisible L 2 (q-1) hLd
  have hlogP : Ordinal.log Ordinal.omega0 P=E := (quadratic_prefix_log L (q-1) hLpos hLd).trans hlogL
  have hshapeP : delta=P+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal) := by
    change delta=thickBlock L 2 (q-1)+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal)
    rw [← thick_block_succ,Nat.sub_add_cancel hq]
    exact hshape
  have hr : Ordinal.omega0*(n : Ordinal) < Ordinal.omega0^(2 : Ordinal) := by
    have h := Ordinal.opow_mul_lt_opow (u := (1 : Ordinal)) (x := (2 : Ordinal)) (Ordinal.natCast_lt_omega0 n) (by norm_num)
    simpa using h
  have hb := original_split_certificate delta P 2 (Ordinal.omega0*(n : Ordinal)) hd hdl hPpos ha (by norm_num) hPd hr hshapeP
  have hR := initial_radius_bounds mu nu delta
  have hPR : actualOrdinalNorm P ≤ R := hb.2.1.trans hR.2.2.2
  have hN2 : actualOrdinalNorm (2 : Ordinal)=2 := by simpa using actualFiniteHeadNorm 0 2
  by_cases hq1 : q=1
  · have hPL : P=L := by simp [P,hq1,thickBlock]
    have hs : Targets.SensitiveUnitSetup f B mu nu P 2 (Ordinal.omega0*(n : Ordinal)) A A' R t := by
      refine ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,le_rfl,hPd,hr,hb.2.2.2.1,hR.1,hR.2.1,hR.2.2.1,hPR,?_,ht,?_,?_,hN,hN',?_⟩
      · rw [hN2]; omega
      · rwa [← hshapeP]
      · rwa [← hshapeP]
      · rwa [hlogP]
    rcases quadraticUnitAdmission f B mu nu P _ A A' R t hs with hdiv | ⟨hadj,hodd,hrest⟩
    · simpa only [hPL] using hdiv
    · exfalso
      apply hfail
      right; right
      rw [hlogP] at hadj hodd
      refine ⟨Or.inr hadj,?_⟩
      have hmin : min (relativeProfile mu E) (relativeProfile nu E)=relativeProfile mu E := min_eq_left hc.le
      by_cases hEeq : E=2
      · right
        refine ⟨n,?_,?_⟩
        · have htwo : Ordinal.omega0^(2 : Ordinal)*2=Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0^(2 : Ordinal) := by
            simpa only [one_add_one_eq_two,mul_one] using (mul_add_one (Ordinal.omega0^(2 : Ordinal)) (1 : Ordinal))
          have hs : delta=Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal) := by
            simpa only [hPL,L,hEeq] using hshapeP
          exact hs.trans (congrArg (fun x : Ordinal => x+Ordinal.omega0*(n : Ordinal)) htwo.symm)
        · change (min (relativeProfile mu E) (relativeProfile nu E)+actualOrdinalNorm (Ordinal.omega0^(2 : Ordinal)))%2=1
          rw [hmin]
          simpa only [hPL,L,hEeq] using hodd
      · left
        have hE3 : (3 : Ordinal) ≤ E := by
          have h := Order.add_one_le_iff.mpr (lt_of_le_of_ne hE2 (Ne.symm hEeq))
          have h23 : (2 : Ordinal)+1=3 := by exact_mod_cast (show (2 : Nat)+1=3 by rfl)
          rwa [h23] at h
        refine ⟨hE3,n,?_,?_⟩
        · simpa only [hPL,L] using hshapeP
        · change (min (relativeProfile mu E) (relativeProfile nu E)+actualOrdinalNorm (Ordinal.omega0^E))%2=1
          rw [hmin]
          simpa only [hPL,L] using hodd
  · have hq2 : 2 ≤ q := by omega
    let Q := thickBlock L 2 (q-2)
    have hQ : Q < epsilonZero := thick_block_below L 2 (q-2) hL ha
    have hQpos : 0 < Q := hLpos.trans_le le_self_add
    have hQd : Ordinal.omega0^(2 : Ordinal) ∣ Q := thick_block_divisible L 2 (q-2) hLd
    have hlogQ : Ordinal.log Ordinal.omega0 Q=E := (quadratic_prefix_log L (q-2) hLpos hLd).trans hlogL
    have hQP : Q+Ordinal.omega0^(2 : Ordinal)=P := by
      have h := thick_block_succ L 2 (q-2)
      rw [show q-2+1=q-1 by omega] at h
      exact h.symm
    have hdoub := double_quadratic_divergence f B hf mu nu Q A A' n R t hmu hnu hQ hA hA' hmud hnud hQpos hQd
      hR.1 hR.2.1 hR.2.2.1 (by rwa [hQP]) ht (by rwa [hQP,← hshapeP]) (by rwa [hQP,← hshapeP]) hN hN' (by rwa [hlogQ])
    obtain ⟨i,hi,hkeep,hkeep'⟩ := hdoub
    exact ⟨i,hi,le_self_add.trans hkeep,le_self_add.trans hkeep'⟩

end LogicLineages.PermittedControl
