module
public import LogicLineages.PermittedControl.OriginalUnitOrderProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem original_split_certificate (delta P a r : Ordinal.{0})
    (hd : delta < epsilonZero) (hdl : Order.IsSuccLimit delta)
    (hPpos : 0 < P) (ha : a < epsilonZero) (hapos : 0 < a)
    (hdiv : Ordinal.omega0^a ∣ P) (hr : r < Ordinal.omega0^a)
    (heq : delta=P+Ordinal.omega0^a+r) :
    P < epsilonZero ∧ actualOrdinalNorm P ≤ actualOrdinalNorm delta ∧
    actualOrdinalNorm a ≤ actualOrdinalNorm delta ∧
    (r=0 ∨ Order.IsSuccLimit r) ∧
    Ordinal.log Ordinal.omega0 delta=Ordinal.log Ordinal.omega0 P ∧
    Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta) ≤ P := by
  have hP : P < epsilonZero := (le_self_add.trans le_self_add).trans_lt (heq ▸ hd)
  have hpow := phase_power_below a ha
  have hrb := hr.trans hpow
  have hblock := epsilonZero_add_principal hpow hrb
  have hbound : Ordinal.omega0^a+r < Ordinal.omega0^(a+1) :=
    Ordinal.isPrincipal_add_omega0_opow _
      ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (Order.lt_add_one_iff.mpr le_rfl))
      (hr.trans ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (Order.lt_add_one_iff.mpr le_rfl)))
  have hsum := (actualDivisiblePrefixNormAddition P _ hP hblock a hdiv hbound).2
  have hblockN : actualOrdinalNorm (Ordinal.omega0^a+r)=1+actualOrdinalNorm a+actualOrdinalNorm r := by
    have hcnf := Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 (one_ne_zero : (1 : Ordinal) ≠ 0) Ordinal.one_lt_omega0 hr
    simp only [mul_one] at hcnf
    rw [actualOrdinalNorm_cnfEquation _ hblock,hcnf]
    simp only [List.map_cons,List.sum_cons,Ordinal.card_one,
      ← actualOrdinalNorm_cnfEquation r hrb]
    norm_num
  have hnorm : actualOrdinalNorm delta=actualOrdinalNorm P+(1+actualOrdinalNorm a+actualOrdinalNorm r) := by
    rw [heq,add_assoc,hsum,hblockN]
  have hprefixl : Order.IsSuccLimit (P+Ordinal.omega0^a) := Ordinal.isSuccLimit_add P
    (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hapos.ne')
  have hrd : r=0 ∨ Order.IsSuccLimit r := by
    have hfixed : actualLimitPart delta=delta := by simpa using limitPart_tail delta hdl 0
    rw [heq,limitPart_add_limit_left _ r hprefixl hrb] at hfixed
    have hrfix : actualLimitPart r=r := add_left_cancel hfixed
    simpa only [hrfix] using limitPart_zero_or_limit r
  have haE : a ≤ Ordinal.log Ordinal.omega0 P := Ordinal.le_log_of_opow_le
    Ordinal.one_lt_omega0 (Ordinal.le_of_dvd hPpos.ne' hdiv)
  have hPb : P < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    Ordinal.lt_opow_of_log_lt Ordinal.one_lt_omega0 (Order.lt_add_one_iff.mpr le_rfl)
  have hbb : Ordinal.omega0^a+r < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    hbound.trans_le ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone (add_le_add_left haE 1))
  have hdb : delta < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) := by
    rw [heq,add_assoc]
    exact Ordinal.isPrincipal_add_omega0_opow _ hPb hbb
  have hlog : Ordinal.log Ordinal.omega0 delta=Ordinal.log Ordinal.omega0 P := by
    apply le_antisymm
    · exact Order.lt_add_one_iff.mp ((Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hdl.bot_lt.ne').mp hdb)
    · exact Ordinal.log_mono_right _ (by rw [heq]; exact le_self_add.trans le_self_add)
  refine ⟨hP,by omega,by omega,hrd,hlog,?_⟩
  rw [hlog]
  exact Ordinal.opow_log_le_self _ hPpos.ne'

 theorem original_high_unit_split (delta : Ordinal.{0}) (hd : delta < epsilonZero)
    (hdl : Order.IsSuccLimit delta) (hx : ∃ x ∈ initialPeelingUnits delta, (2 : Ordinal) < x) :
    ∃ P a r : Ordinal.{0}, 0 < P ∧ a < epsilonZero ∧ 2 < a ∧
      Ordinal.omega0^a ∣ P ∧ r < Ordinal.omega0^a ∧ delta=P+Ordinal.omega0^a+r := by
  obtain ⟨an,han⟩ := normalRepresentationComplete delta hd
  obtain ⟨an,hnf⟩ := an
  subst delta
  cases an with
  | zero => exact False.elim (hdl.bot_lt.ne' rfl)
  | oadd e c t =>
    have he : e.repr < epsilonZero := normalRepresentationSound ⟨e,hnf.fst⟩
    have hlog : Ordinal.log Ordinal.omega0 (ONote.oadd e c t).repr=e.repr := by
      change Ordinal.log Ordinal.omega0 (Ordinal.omega0^e.repr*(c : Ordinal)+t.repr)=_
      rw [Ordinal.log_opow_mul_add Ordinal.one_lt_omega0 (by exact_mod_cast c.ne_zero) hnf.snd'.repr_lt,
        Ordinal.log_eq_zero (Ordinal.natCast_lt_omega0 (c : Nat)),add_zero]
    obtain ⟨x,hx,hx2⟩ := hx
    have hxall : x ∈ originalGapUnits (ONote.oadd e c t).repr :=
      List.mem_of_mem_tail (List.mem_reverse.mp hx)
    obtain ⟨p,hp,hpx⟩ := List.mem_map.mp (original_unit_cnf _ x hxall)
    have he2 : (2 : Ordinal) < e.repr := by
      have hb := Ordinal.CNF.fst_le_log hp
      rw [hlog,hpx] at hb
      exact hx2.trans_le hb
    by_cases hc : 2 ≤ (c : Nat)
    · let P := Ordinal.omega0^e.repr*((c-1 : Nat) : Ordinal)
      have hcpos : 0 < ((c-1 : Nat) : Ordinal) := by exact_mod_cast (by omega : 0 < (c : Nat)-1)
      have heq : (ONote.oadd e c t).repr=P+Ordinal.omega0^e.repr+t.repr := by
        change Ordinal.omega0^e.repr*(c : Ordinal)+t.repr=_
        have hcast : (c : Ordinal)=((c-1 : Nat) : Ordinal)+1 := by
          rw [← Nat.cast_add_one]
          congr 1
          omega
        rw [hcast,mul_add_one]
      exact ⟨P,e.repr,t.repr,mul_pos (Ordinal.opow_pos _ Ordinal.omega0_pos) hcpos,he,he2,
        ⟨_,rfl⟩,hnf.snd'.repr_lt,heq⟩
    · have hc1 : (c : Nat)=1 := by have := c.pos; omega
      have hxTail : x ∈ originalGapUnits t.repr := by
        change x ∈ (originalGapUnits (ONote.oadd e c t).repr).tail.reverse at hx
        rw [original_units_oadd e t c hnf,hc1] at hx
        simpa using hx
      cases t with
      | zero => simpa [originalGapUnits,ONote.repr] using hxTail
      | oadd a d r =>
        have hnf' := hnf.snd
        have ha : a.repr < epsilonZero := normalRepresentationSound ⟨a,hnf'.fst⟩
        have hlog' : Ordinal.log Ordinal.omega0 (ONote.oadd a d r).repr=a.repr := by
          change Ordinal.log Ordinal.omega0 (Ordinal.omega0^a.repr*(d : Ordinal)+r.repr)=_
          rw [Ordinal.log_opow_mul_add Ordinal.one_lt_omega0 (by exact_mod_cast d.ne_zero) hnf'.snd'.repr_lt,
            Ordinal.log_eq_zero (Ordinal.natCast_lt_omega0 (d : Nat)),add_zero]
        obtain ⟨p,hp,hpx⟩ := List.mem_map.mp (original_unit_cnf _ x hxTail)
        have ha2 : (2 : Ordinal) < a.repr := by
          have hb := Ordinal.CNF.fst_le_log hp
          rw [hlog',hpx] at hb
          exact hx2.trans_le hb
        let P := Ordinal.omega0^e.repr+Ordinal.omega0^a.repr*((d-1 : Nat) : Ordinal)
        have hPpos : 0 < P := (Ordinal.opow_pos e.repr Ordinal.omega0_pos).trans_le le_self_add
        have hdiv : Ordinal.omega0^a.repr ∣ P :=
          ((Ordinal.opow_dvd_opow Ordinal.omega0 hnf.snd'.lt.le).add (dvd_mul_right _ _))
        have heq : (ONote.oadd e c (ONote.oadd a d r)).repr=P+Ordinal.omega0^a.repr+r.repr := by
          change Ordinal.omega0^e.repr*(c : Ordinal)+(Ordinal.omega0^a.repr*(d : Ordinal)+r.repr)=_
          have hcast : (d : Ordinal)=((d-1 : Nat) : Ordinal)+1 := by
            rw [← Nat.cast_add_one]
            congr 1
            have := d.pos
            omega
          rw [show (c : Ordinal)=1 by exact_mod_cast hc1,mul_one,hcast,mul_add_one]
          simp only [P,add_assoc]
        exact ⟨P,a.repr,r.repr,hPpos,ha,ha2,hdiv,hnf'.snd'.repr_lt,heq⟩

end LogicLineages.PermittedControl
