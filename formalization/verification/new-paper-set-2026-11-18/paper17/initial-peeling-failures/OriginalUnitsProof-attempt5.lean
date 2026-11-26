module
public import LogicLineages.PermittedControl.InitialNormProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem original_units_oadd (e t : ONote) (c : PNat) (h : ONote.NF (.oadd e c t)) :
    originalGapUnits (ONote.oadd e c t).repr =
      List.replicate (c : Nat) e.repr ++ originalGapUnits t.repr := by
  have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
  have hcnf := Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc (Ordinal.natCast_lt_omega0 (c : Nat)) h.snd'.repr_lt
  change originalGapUnits (Ordinal.omega0^e.repr*(c : Ordinal)+t.repr) = _
  simp only [originalGapUnits,hcnf,List.flatMap_cons,Ordinal.card_nat,Cardinal.toNat_natCast]

private theorem original_units_raw_eval (a : ONote) (ha : ONote.NF a) :
    ((originalGapUnits a.repr).map (fun e => Ordinal.omega0^e)).sum=a.repr := by
  induction a with
  | zero => simp [originalGapUnits,ONote.repr]
  | oadd e c t ihe iht =>
    rw [original_units_oadd e t c ha,List.map_append,List.sum_append,List.map_replicate,List.sum_replicate,
      Ordinal.nsmul_eq_mul,iht ha.snd]
    rfl

 theorem original_units_eval (delta : Ordinal.{0}) (hd : delta < epsilonZero) :
    ((originalGapUnits delta).map (fun e => Ordinal.omega0^e)).sum=delta := by
  obtain ⟨a,rfl⟩ := normalRepresentationComplete delta hd
  exact original_units_raw_eval a.1 a.2

private theorem original_units_raw_weight (a : ONote) (ha : ONote.NF a) :
    ((originalGapUnits a.repr).map (fun e => 1+actualOrdinalNorm e)).sum=Vendor.R1.treeWeight a := by
  induction a with
  | zero => simp [originalGapUnits,ONote.repr,Vendor.R1.treeWeight]
  | oadd e c t ihe iht =>
    rw [original_units_oadd e t c ha,List.map_append,List.sum_append,List.map_replicate,List.sum_replicate,
      iht ha.snd,actualOrdinalNorm_notationCorrespondence (⟨e,ha.fst⟩ : NONote)]
    rfl

 theorem original_units_weight (delta : Ordinal.{0}) (hd : delta < epsilonZero) :
    ((originalGapUnits delta).map (fun e => 1+actualOrdinalNorm e)).sum=actualOrdinalNorm delta := by
  obtain ⟨a,rfl⟩ := normalRepresentationComplete delta hd
  rw [actualOrdinalNorm_notationCorrespondence a]
  exact original_units_raw_weight a.1 a.2

 theorem original_units_head (delta : Ordinal.{0}) (hd : delta < epsilonZero) (hpos : delta ≠ 0) :
    ∃ l : List Ordinal, originalGapUnits delta=Ordinal.log Ordinal.omega0 delta :: l := by
  obtain ⟨a,rfl⟩ := normalRepresentationComplete delta hd
  obtain ⟨a,ha⟩ := a
  cases a with
  | zero => exact False.elim (hpos rfl)
  | oadd e c t =>
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hlog : Ordinal.log Ordinal.omega0 (ONote.oadd e c t).repr=e.repr := by
      change Ordinal.log Ordinal.omega0 (Ordinal.omega0^e.repr*(c : Ordinal)+t.repr)=_
      rw [Ordinal.log_opow_mul_add Ordinal.one_lt_omega0 hc ha.snd'.repr_lt,
        Ordinal.log_eq_zero (Ordinal.natCast_lt_omega0 (c : Nat)),add_zero]
    rw [original_units_oadd e t c ha,hlog]
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero c.ne_zero
    rw [hn,List.replicate_succ,List.cons_append]
    exact ⟨_,rfl⟩

 theorem original_units_positive (delta : Ordinal.{0}) (hd : delta < epsilonZero)
    (hl : Order.IsSuccLimit delta) (e : Ordinal.{0}) (he : e ∈ originalGapUnits delta) : 1 ≤ e := by
  have hfixed : Ordinal.omega0*(delta/Ordinal.omega0)=delta := by simpa using limitPart_tail delta hl 0
  have hdiv : Ordinal.omega0^(1 : Ordinal) ∣ delta := by
    rw [Ordinal.opow_one]
    exact ⟨delta/Ordinal.omega0,hfixed.symm⟩
  have hmin := (actualMinExponentDivisibility delta hd 1).mpr hdiv
  obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp he
  have heq : e=p.1 := (List.mem_replicate.mp he).2
  subst e
  exact hmin p hp

 theorem initial_no_sensitive_shape (delta : Ordinal.{0}) (hd : delta < epsilonZero)
    (hl : Order.IsSuccLimit delta) (hs : ∀ e ∈ initialPeelingUnits delta, e < 2) :
    ∃ n : Nat, delta=Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)+Ordinal.omega0*(n : Ordinal) := by
  obtain ⟨l,hlst⟩ := original_units_head delta hd hl.bot_lt.ne'
  have hones : ∀ e ∈ l, e=(1 : Ordinal) := by
    intro e he
    have hp := original_units_positive delta hd hl e (by rw [hlst]; exact List.mem_cons_of_mem _ he)
    have hlt := hs e (by simpa only [initialPeelingUnits,hlst,List.tail_cons,List.mem_reverse] using he)
    exact le_antisymm (Order.lt_add_one_iff.mp hlt) hp
  have hlrep : l=List.replicate l.length (1 : Ordinal) := List.eq_replicate_length.mpr hones
  have heval := original_units_eval delta hd
  rw [hlst,List.map_cons,List.sum_cons,hlrep,List.map_replicate,List.sum_replicate,
    Ordinal.opow_one,Ordinal.nsmul_eq_mul] at heval
  exact ⟨l.length,heval.symm⟩

end LogicLineages.PermittedControl
