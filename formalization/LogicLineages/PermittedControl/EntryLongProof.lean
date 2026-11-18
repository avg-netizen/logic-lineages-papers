module
public import LogicLineages.PermittedControl.EntryPrefixProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

theorem firstEntry_step (f : Nat → Nat) (a nu : Ordinal.{0}) (i : Nat)
    (hn : ¬ (nu ≤ a ∧ a < nu + Ordinal.omega0)) (hi : FirstEntry f (descentWith f a) nu i) :
    FirstEntry f a nu (i+1) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Function.iterate_succ_apply] using hi.1
  · simpa only [Function.iterate_succ_apply] using hi.2.1
  · intro j hj hh
    cases j with
    | zero => exact hn hh
    | succ j => exact hi.2.2 j (by omega) (by simpa only [Function.iterate_succ_apply] using hh)

theorem selected_potential (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m t : Nat) (hm : 0 < m) (ht : max m B ≤ t) :
    Int.ModEq (m : Int) (potential (f t) : Int) ((potential t : Int)-1) := by
  simpa using selected_orbit f B hf m t 1 hm ht

theorem long_entry_state (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m : Nat) (hm : 0 < m) (nu P : Ordinal.{0}) (j : Nat)
    (hnu : nu = 0 ∨ Order.IsSuccLimit nu) (hP : P < epsilonZero)
    (hdiv : Ordinal.omega0 ^ (2 : Ordinal.{0}) ∣ P)
    (hnuEq : nu = P+Ordinal.omega0*(j : Ordinal))
    (hnuNorm : actualOrdinalNorm nu = actualOrdinalNorm P+2*j)
    (a : Ordinal.{0}) (ha : a < epsilonZero)
    (hhigh : P+Ordinal.omega0 ^ (2 : Ordinal.{0}) ≤ actualLimitPart a)
    (ht : max (actualOrdinalNorm nu+3) (max m B) ≤ actualOrdinalNorm a) :
    ∃ i : Nat, 0 < i ∧ FirstEntry f a nu i ∧
      Int.ModEq (m : Int) (i : Int)
        ((potential (actualOrdinalNorm a) : Int)-(((actualOrdinalNorm nu+1)/2 : Nat) : Int)) := by
  have had := selected_threshold_admissible f B hf
  have hpow : Ordinal.omega0 ^ (2 : Ordinal.{0}) < Ordinal.omega0 ^ ((2 : Ordinal)+1) :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Order.lt_add_one_iff.mpr le_rfl)
  have hsigma := actualDivisiblePrefixNormAddition P (Ordinal.omega0 ^ (2 : Ordinal))
    hP square_facts.1 2 hdiv hpow
  have hsigNorm : actualOrdinalNorm (P+Ordinal.omega0 ^ (2 : Ordinal.{0})) = actualOrdinalNorm P+3 := by
    rw [hsigma.2,square_facts.2.1]
  have hsigLim := Ordinal.isSuccLimit_add P square_facts.2.2
  have hnuBelow : nu+Ordinal.omega0 < P+Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
    rw [hnuEq,add_assoc]
    apply (add_lt_add_iff_left P).mpr
    have h := linear_below_square (j+1) 0
    simpa only [Nat.cast_add,Nat.cast_one,mul_add,mul_one,Nat.cast_zero,add_zero] using h
  have hnuEps : nu < epsilonZero := (lt_of_le_of_lt le_self_add hnuBelow).trans hsigma.1
  revert ha hhigh ht
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro ha hhigh ht
    have hw : Ordinal.omega0 ≤ a := (Ordinal.omega0_le_of_isSuccLimit hsigLim).trans
      (hhigh.trans (Ordinal.mul_div_le a Ordinal.omega0))
    have hno : ¬ (nu ≤ a ∧ a < nu+Ordinal.omega0) := by
      intro h
      exact (not_lt_of_ge (hnuBelow.le.trans (hhigh.trans (Ordinal.mul_div_le a Ordinal.omega0)))) h.2
    have hd := descent_strict f a hw ha
    have hn := descent_norm f a hw ha
    have hb : actualOrdinalNorm nu+3 ≤ f (actualOrdinalNorm a) :=
      (by omega : actualOrdinalNorm nu+3 ≤ actualOrdinalNorm a).trans (control_self_le f had.2 _)
    have hp := selected_potential f B hf m (actualOrdinalNorm a) hm (by omega)
    by_cases heq : actualLimitPart a = P+Ordinal.omega0 ^ (2 : Ordinal.{0})
    · let b := f (actualOrdinalNorm a)
      let q := (b-actualOrdinalNorm P)/2
      let r := (b-actualOrdinalNorm P)%2
      have hmin : actualMinExponentAtLeast P (2 : Ordinal) := (actualMinExponentDivisibility P hP 2).mpr hdiv
      have hmax := actualDivisiblePrefixMaximum P (Ordinal.omega0 ^ (2 : Ordinal)) hP square_facts.1
        square_facts.2.2.bot_lt 2 hmin hpow b (by dsimp [b]; omega)
      have hbudget : 2 ≤ b-actualOrdinalNorm P := by dsimp [b]; omega
      have hstep : descentWith f a = P+(Ordinal.omega0*(q : Ordinal)+(r : Ordinal)) := by
        unfold descentWith
        rw [heq,hmax,actualOmegaSquaredMaximum _ hbudget]
      have hq : j ≤ q := by dsimp [q,b]; omega
      have hstate : descentWith f a = nu+(Ordinal.omega0*((q-j : Nat) : Ordinal)+(r : Ordinal)) := by
        rw [hstep,hnuEq,add_assoc,← add_assoc (Ordinal.omega0 * (j : Ordinal)),← mul_add]
        simp only [← Nat.cast_add, Nat.add_sub_of_le hq]
      have hentry := linear_entry f had.2 nu hnu hnuEps (q-j) r
      rw [← hstate] at hentry
      refine ⟨q-j+1,by omega,firstEntry_step f a nu (q-j) hno hentry,?_⟩
      have heven := Nat.mod_eq_zero_of_dvd (selected_even f B hf (actualOrdinalNorm a))
      have hcount : ((q-j+1 : Nat) : Int) =
          (potential b : Int)+1-(((actualOrdinalNorm nu+1)/2 : Nat) : Int) := by
        dsimp [q,b,potential]
        omega
      rw [hcount]
      have h := hp.add_right (1-(((actualOrdinalNorm nu+1)/2 : Nat) : Int))
      convert h using 1 <;> dsimp [b] <;> omega
    · have hlt : P+Ordinal.omega0 ^ (2 : Ordinal) < actualLimitPart a := lt_of_le_of_ne hhigh (Ne.symm heq)
      have hdecomp := actualNonfiniteDecomposition a hw ha
      have hm := actualMaximumPredecessor_correct (actualLimitPart a) hdecomp.2.1.bot_lt hdecomp.1 (f (actualOrdinalNorm a))
      have hbudget : actualOrdinalNorm (P+Ordinal.omega0 ^ (2 : Ordinal)) ≤ f (actualOrdinalNorm a) := by
        rw [hsigNorm]
        omega
      have hstep : P+Ordinal.omega0 ^ (2 : Ordinal) ≤ descentWith f a := hm.2 ⟨hlt,hbudget⟩
      have hlp : P+Ordinal.omega0 ^ (2 : Ordinal) ≤ actualLimitPart (descentWith f a) := by
        have h := actualLimitPartMonotone hstep
        have he : actualLimitPart (P+Ordinal.omega0 ^ (2 : Ordinal)) = P+Ordinal.omega0 ^ (2 : Ordinal) := by
          simpa using limitPart_tail _ hsigLim 0
        rwa [he] at h
      have ht' : max (actualOrdinalNorm nu+3) (max m B) ≤ actualOrdinalNorm (descentWith f a) := by
        rw [hn]
        exact ht.trans (control_self_le f had.2 _)
      obtain ⟨i,hip,hi,hres⟩ := ih (descentWith f a) hd (hd.trans ha) hlp ht'
      refine ⟨i+1,by omega,firstEntry_step f a nu i hno hi,?_⟩
      rw [hn] at hres
      have h := (hres.trans (hp.sub_right (((actualOrdinalNorm nu+1)/2 : Nat) : Int))).add_right 1
      convert h using 1 <;> (try simp only [Int.natCast_add,Int.natCast_one]) <;> omega

end LogicLineages.PermittedControl
