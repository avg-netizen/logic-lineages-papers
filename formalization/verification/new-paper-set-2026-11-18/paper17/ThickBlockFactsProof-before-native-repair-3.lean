module
public import LogicLineages.PermittedControl.ThickBlockTargets
public import LogicLineages.PermittedControl.RetainedPhaseProof
public import LogicLineages.PermittedControl.TargetVisitProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem thick_monomial_norm (a : Ordinal.{0}) (ha : a < epsilonZero) (q : Nat) :
    actualOrdinalNorm (Ordinal.omega0^a*(q : Ordinal)) = q*(1+actualOrdinalNorm a) := by
  have hp := phase_power_below a ha
  have hb := epsilonZero_add_principal.mul_natCast_lt hp q
  cases q with
  | zero =>
    have hz : actualOrdinalNorm 0=0 := by simpa using actualFiniteHeadNorm 0 0
    simpa using hz
  | succ q =>
    have hc : ((q+1 : Nat) : Ordinal) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
    have hcnf := Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
      (Ordinal.natCast_lt_omega0 (q+1)) (Ordinal.opow_pos a Ordinal.omega0_pos)
    rw [actualOrdinalNorm_cnfEquation _ hb]
    simpa only [add_zero, Ordinal.CNF.zero_right, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, Ordinal.card_nat, Cardinal.toNat_natCast] using
      congrArg (fun l : List (Ordinal×Ordinal) =>
        (l.map (fun p => p.2.card.toNat*(1+actualOrdinalNorm p.1))).sum) hcnf

 theorem thick_block_below (P a : Ordinal.{0}) (q : Nat) (hP : P < epsilonZero) (ha : a < epsilonZero) :
    thickBlock P a q < epsilonZero :=
  epsilonZero_add_principal hP (epsilonZero_add_principal.mul_natCast_lt (phase_power_below a ha) q)

 theorem thick_block_divisible (P a : Ordinal.{0}) (q : Nat) (hd : Ordinal.omega0^a ∣ P) :
    Ordinal.omega0^a ∣ thickBlock P a q := by
  obtain ⟨z,hz⟩ := hd
  refine ⟨z+(q : Ordinal), ?_⟩
  simp only [thickBlock,hz,mul_add]

 theorem thick_block_norm (P a : Ordinal.{0}) (q : Nat) (hP : P < epsilonZero)
    (ha : a < epsilonZero) (hd : Ordinal.omega0^a ∣ P) :
    actualOrdinalNorm (thickBlock P a q) = actualOrdinalNorm P+q*(1+actualOrdinalNorm a) := by
  have hw := epsilonZero_add_principal.mul_natCast_lt (phase_power_below a ha) q
  have hbound : Ordinal.omega0^a*(q : Ordinal) < Ordinal.omega0^(a+1) :=
    Ordinal.opow_mul_lt_opow (Ordinal.natCast_lt_omega0 q) (Order.lt_add_one_iff.mpr le_rfl)
  exact (actualDivisiblePrefixNormAddition P _ hP hw a hd hbound).2.trans
    (congrArg (fun n => actualOrdinalNorm P+n) (thick_monomial_norm a ha q))

 theorem thick_block_positive (P a : Ordinal.{0}) (q : Nat) (hq : 0 < q) : 0 < thickBlock P a q := by
  have hqo : 0 < (q : Ordinal) := by exact_mod_cast hq
  exact (mul_pos (Ordinal.opow_pos a Ordinal.omega0_pos) hqo).trans_le le_add_self

 theorem thick_block_limit (P a : Ordinal.{0}) (q : Nat) (ha : 0 < a) (hq : 0 < q) :
    Order.IsSuccLimit (thickBlock P a q) := by
  have hpow : Order.IsSuccLimit (Ordinal.omega0^a) :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 ha.ne'
  exact Ordinal.isSuccLimit_add P
    (Ordinal.isSuccLimit_mul_left hpow (by exact_mod_cast hq))

 theorem thick_block_leading (P a : Ordinal.{0}) (q : Nat) (hq : 0 < q)
    (hd : Ordinal.omega0^a ∣ P) :
    Ordinal.log Ordinal.omega0 (thickBlock P a q) =
      if P=0 then a else Ordinal.log Ordinal.omega0 P := by
  have hc : (q : Ordinal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  by_cases hP : P=0
  · subst P
    simp only [thickBlock,zero_add,if_pos rfl]
    rw [Ordinal.log_opow_mul Ordinal.one_lt_omega0 a hc,
      Ordinal.log_eq_zero (Ordinal.natCast_lt_omega0 q),add_zero]
    simp
  · rw [if_neg hP]
    have hae := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 (Ordinal.le_of_dvd hP hd)
    have hPb : P < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
      Ordinal.lt_opow_of_log_lt Ordinal.one_lt_omega0 (Order.lt_add_one_iff.mpr le_rfl)
    have hmb : Ordinal.omega0^a*(q : Ordinal) < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
      Ordinal.opow_mul_lt_opow (Ordinal.natCast_lt_omega0 q) (Order.lt_add_one_iff.mpr hae)
    have hb := Ordinal.isPrincipal_add_omega0_opow _ hPb hmb
    apply le_antisymm
    · exact Order.lt_add_one_iff.mp ((Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0
        (thick_block_positive P a q hq).ne').mp hb)
    · exact Ordinal.log_mono_right _ le_self_add

 theorem thick_head_norm (mu P a : Ordinal.{0}) (q : Nat) (hmu : mu < epsilonZero)
    (hP : P < epsilonZero) (ha : a < epsilonZero) (hq : 0 < q) (hd : Ordinal.omega0^a ∣ P) :
    actualOrdinalNorm (mu+thickBlock P a q) = actualOrdinalNorm P+q*(1+actualOrdinalNorm a)+
      relativeProfile mu (if P=0 then a else Ordinal.log Ordinal.omega0 P) := by
  rw [(relativeNorm mu _ hmu (thick_block_below P a q hP ha)).1,
    thick_block_norm P a q hP ha hd]
  simp only [relativeCost,if_neg (thick_block_positive P a q hq).ne',thick_block_leading P a q hq hd]

 theorem thick_head_suffix_norm (mu P a r : Ordinal.{0}) (q : Nat) (hmu : mu < epsilonZero)
    (hP : P < epsilonZero) (ha : a < epsilonZero) (hq : 0 < q) (hd : Ordinal.omega0^a ∣ P)
    (hr : r < Ordinal.omega0^a) :
    actualOrdinalNorm (mu+(thickBlock P a q+r)) =
      actualOrdinalNorm (mu+thickBlock P a q)+actualOrdinalNorm r := by
  have hb := thick_block_below P a q hP ha
  have hx := epsilonZero_add_principal hb (hr.trans (phase_power_below a ha))
  have hf := retained_prefix_cost mu (thickBlock P a q) a r hmu hb ha
    (thick_block_positive P a q hq) (thick_block_divisible P a q hd) hr
  rw [(relativeNorm mu _ hmu hx).1,hf.1,hf.2,(relativeNorm mu _ hmu hb).1]
  simp only [relativeCost,if_neg (thick_block_positive P a q hq).ne']
  omega

 theorem thick_exponent_norm (a : Ordinal.{0}) (ha : a < epsilonZero) (h2 : (2 : Ordinal) ≤ a) :
    2 ≤ actualOrdinalNorm a := by
  by_cases hn : Ordinal.omega0 ≤ a
  · exact nonfinite_norm a ha hn
  · obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp (lt_of_not_ge hn)
    have hNat : 2 ≤ n := by exact_mod_cast h2
    have hnorm : actualOrdinalNorm (n : Ordinal) = n := by simpa using actualFiniteHeadNorm 0 n
    rwa [hnorm]

 theorem actual_phase_normalize (f : Nat → Nat) (A L : Ordinal.{0}) (t : Nat)
    (hL : L < epsilonZero) (hlim : L=0 ∨ Order.IsSuccLimit L)
    (hpart : actualLimitPart A=L) (hnorm : actualOrdinalNorm A=t) : A=countInitial L t := by
  have hi : FirstEntry f A L 0 := by
    have h := (interval_iff_limitPart A L hlim).mpr hpart
    exact ⟨h.1,h.2,by intro j hj; omega⟩
  exact actual_entry_reset f A L 0 t hL hi hnorm

 theorem thickBlockTailEffective : Targets.ThickBlockTailEffective := by
  have hR : Primrec (fun z : Nat×Nat => z.1) := Primrec.fst
  have hB : Primrec (fun z : Nat×Nat => z.2) := Primrec.snd
  have hp : Primrec₂ (fun x y : Nat => x^y) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hpow := hp.comp (Primrec.nat_add.comp hR (Primrec.const 2)) (Primrec.const 4)
  exact Primrec.nat_max.comp (Primrec.nat_mul.comp (Primrec.const 100) hpow)
    (Primrec.nat_max.comp (initialLcm_primrec.comp (Primrec.nat_add.comp hR (Primrec.const 1))) hB)

 theorem thick_block_succ (P a : Ordinal.{0}) (q : Nat) :
    thickBlock P a (q+1)=thickBlock P a q+Ordinal.omega0^a := by
  simp [thickBlock,Nat.cast_add,mul_add,add_assoc]

 theorem thick_block_mono (P a : Ordinal.{0}) : Monotone (thickBlock P a) := by
  intro i j hij
  exact (add_le_add_iff_left P).mpr
    ((Ordinal.isNormal_mul_right (Ordinal.opow_pos a Ordinal.omega0_pos)).monotone (by exact_mod_cast hij))

 theorem thick_block_strict (P a : Ordinal.{0}) : StrictMono (thickBlock P a) := by
  intro i j hij
  exact (add_lt_add_iff_left P).mpr
    ((Ordinal.isNormal_mul_right (Ordinal.opow_pos a Ordinal.omega0_pos)).strictMono (by exact_mod_cast hij))

 theorem thick_head_drop (mu P a : Ordinal.{0}) (q : Nat) (hmu : mu < epsilonZero)
    (hP : P < epsilonZero) (ha : a < epsilonZero) (hq : 0 < q) (hd : Ordinal.omega0^a ∣ P) :
    actualOrdinalNorm (mu+thickBlock P a (q+1)) =
      actualOrdinalNorm (mu+thickBlock P a q)+(1+actualOrdinalNorm a) := by
  rw [thick_head_norm mu P a (q+1) hmu hP ha (by omega) hd,
    thick_head_norm mu P a q hmu hP ha hq hd]
  simp only [Nat.add_mul,one_mul]
  omega

 theorem entry_norm_ge_target (f : Nat → Nat) (A target : Ordinal.{0}) (i E : Nat)
    (ht : target < epsilonZero) (hi : FirstEntry f A target i) (hE : entryNormAt f A i=E) :
    actualOrdinalNorm target ≤ E := by
  obtain ⟨n,hn⟩ := interval_tail ((descentWith f)^[i] A) target hi.1 hi.2.1
  have hf := (actualFiniteTailClosureNorm target ht n).2
  change actualOrdinalNorm ((descentWith f)^[i] A)=E at hE
  rw [hn,hf] at hE
  omega

 theorem target_next_relative (f : Nat → Nat) (A mu rho : Ordinal.{0}) (i E : Nat)
    (hr : Order.IsSuccLimit rho) (hi : FirstEntry f A (mu+rho) i) (hE : entryNormAt f A i=E) :
    (descentWith f)^[i+1] A-mu = relativeMaximum mu rho (f E) := by
  have hp := (interval_iff_limitPart ((descentWith f)^[i] A) (mu+rho)
    (Or.inr (Ordinal.isSuccLimit_add mu hr))).mp ⟨hi.1,hi.2.1⟩
  rw [Function.iterate_succ_apply']
  unfold descentWith
  rw [hp]
  change actualMaximumPredecessor (mu+rho) (f (entryNormAt f A i))-mu = _
  rw [hE]
  rfl

end LogicLineages.PermittedControl
