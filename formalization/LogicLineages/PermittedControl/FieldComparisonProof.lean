module
public import LogicLineages.PermittedControl.FieldComparisonTargets
import LogicLineages.PermittedControl.FieldComparisonPeelProof
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.InverseTableProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-! Arithmetic over abstract naturals. -/

theorem tail_four (A B C D x : Nat) (h : max (max A B) (max C D) ≤ x) :
    A ≤ x ∧ B ≤ x ∧ C ≤ x ∧ D ≤ x := by omega

theorem tail_five (A B C D E x : Nat) (h : max (max A B) (max (max C D) E) ≤ x) :
    A ≤ x ∧ B ≤ x ∧ C ≤ x ∧ D ≤ x ∧ E ≤ x := by omega

theorem sign_cases (s : Nat) (h : s ≤ 2) : s = 0 ∨ s = 1 ∨ s = 2 := by omega

theorem peel_exponent (a b : Nat) : a + (b - a) = b + (a - b) := by omega

/-! Controls. -/

theorem iterate_exponent_strict (f : Nat → Nat) (hlt : ∀ n, n < f n) (x : Nat) :
    StrictMono (fun i : Nat => f^[i] x) :=
  strictMono_nat_of_lt_succ (fun i => by
    show f^[i] x < f^[i+1] x
    rw [Function.iterate_succ_apply']
    exact hlt _)

theorem selected_strict (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B) (n : Nat) :
    n < f n :=
  (self_lt_Phi n).trans_le ((selected_threshold_admissible f B hf).2 n)

/-! The normalizer on two entry fields, with its case split made explicit. -/

theorem distinctForm_entry_entry (a b : Nat) (lp mp lq mq : NONote) :
    distinctForm (.entry a lp mp) (.entry b lq mq) =
      if NONote.cmp (lq - (mq + omegaMultiple (a - b))) (lp - (mp + omegaMultiple (b - a))) =
          Ordering.lt then
        ComparisonForm.linear (equalGapCertificateCode (rawNoteEncode (mp + omegaMultiple (b - a)).1)
          (rawNoteEncode (mq + omegaMultiple (a - b)).1)
          (rawNoteEncode (lq - (mq + omegaMultiple (a - b))).1))
          (.entry 0 lp ((mp + omegaMultiple (b - a)) + (lq - (mq + omegaMultiple (a - b)))))
      else ComparisonForm.const 0 := by
  simp only [distinctForm]
  cases NONote.cmp (lq - (mq + omegaMultiple (a - b))) (lp - (mp + omegaMultiple (b - a))) <;>
    rfl

theorem sameForm_entry_entry (a b : Nat) (lp mp lq mq : NONote) :
    sameForm (.entry a lp mp) (.entry b lq mq) =
      if NONote.cmp (lp - (mp + omegaMultiple (b - a))) (lq - (mq + omegaMultiple (a - b))) =
          Ordering.lt then 0
      else if NONote.cmp (lp - (mp + omegaMultiple (b - a))) (lq - (mq + omegaMultiple (a - b))) =
          Ordering.gt then 2
      else equalGapCertificateCode (rawNoteEncode (mp + omegaMultiple (b - a)).1)
        (rawNoteEncode (mq + omegaMultiple (a - b)).1)
        (rawNoteEncode (lp - (mp + omegaMultiple (b - a))).1) := by
  simp only [sameForm]
  cases NONote.cmp (lp - (mp + omegaMultiple (b - a))) (lq - (mq + omegaMultiple (a - b))) <;>
    rfl

/-! Peeled entries of a long field. -/

/-- A sufficient tail for peeling `c` applications off `(λ, μ)`. -/
noncomputable def peelTail (B : Nat) (lam mu : NONote) (c : Nat) : Nat :=
  max (max 2 (max (actualOrdinalNorm lam.1.repr)
    (max (actualOrdinalNorm (mu.1.repr + Ordinal.omega0 * (c : Ordinal)))
      (actualOrdinalNorm mu.1.repr))))
    (max (actualOrdinalNorm mu.1.repr + 3) (max 1 B))

theorem peeled_proper (a : Nat) (lam mu : NONote) (hL : LongField (.entry a lam mu)) (c : Nat) :
    ((mu + omegaMultiple c).1.repr = 0 ∨ Order.IsSuccLimit (mu + omegaMultiple c).1.repr) ∧
    (mu + omegaMultiple c).1.repr < lam.1.repr := by
  obtain ⟨hll,hmu,hml,hlong⟩ := hL
  rw [peeled_repr]
  exact ⟨peeled_endpoint _ hmu c,
    long_peel_bound _ _ (hml.trans (normalRepresentationSound lam)) hmu hll hml hlong c⟩

theorem peeled_value (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B) (a : Nat)
    (lam mu : NONote) (hL : LongField (.entry a lam mu)) (c x : Nat)
    (hx : peelTail B lam mu c ≤ x) :
    ∃ i : Nat, FirstEntry f (countInitial lam.1.repr x) (mu + omegaMultiple c).1.repr i ∧
      x ≤ entryNormAt f (countInitial lam.1.repr x) i ∧
      FieldValue f (.entry a lam mu) x (f^[a + c] (entryNormAt f (countInitial lam.1.repr x) i)) := by
  obtain ⟨hll,hmu,hml,hlong⟩ := hL
  have hlamE := normalRepresentationSound lam
  have hlt := long_peel_bound lam.1.repr mu.1.repr (hml.trans hlamE) hmu hll hml hlong c
  obtain ⟨i,k,hi,hk,hnorm,hxe⟩ := entry_peel f B hf lam.1.repr mu.1.repr c x hlamE hll hmu hlt hx
  refine ⟨i,?_,hxe,k,hk,?_⟩
  · rw [peeled_repr]
    exact hi
  · rw [hnorm,Function.iterate_add_apply]

/-! The order branch `x < y`. -/

theorem distinct_iterate_iterate (f : Nat → Nat) (hmono : StrictMono f) (hinfl : ∀ n, n ≤ f n)
    (m n : Nat) :
    ∃ T : Nat, ∀ x y : Nat, T ≤ x → x < y →
      ∃ vF vG : Nat, FieldValue f (.iterate m) x vF ∧ FieldValue f (.iterate n) y vG ∧
        FormHolds f (distinctForm (.iterate m) (.iterate n)) x y vF vG := by
  refine ⟨0,fun x y _ hxy => ⟨f^[m] x,f^[n] y,rfl,rfl,?_⟩⟩
  by_cases hmn : m ≤ n
  · rw [distinctForm,if_pos hmn]
    apply comparison_lt
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hmn
    calc f^[m] x < f^[m] y := hmono.iterate m hxy
      _ ≤ f^[m + d] y := by
        rw [Function.iterate_add_apply]
        exact (hmono.iterate m).monotone (iterate_self_le hinfl d y)
  · rw [distinctForm,if_neg hmn]
    refine ⟨f^[m - n] x,rfl,?_⟩
    have hv : f^[m] x = f^[n] (f^[m - n] x) := by
      rw [← Function.iterate_add_apply,Nat.add_sub_cancel' (Nat.le_of_not_le hmn)]
    rw [hv]
    exact rows_exact (f^[n]) (hmono.iterate n) y _

theorem distinct_iterate_entry (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m b : Nat) (lq mq : NONote) (hG : LongField (.entry b lq mq)) :
    ∃ T : Nat, ∀ x y : Nat, T ≤ x → x < y →
      ∃ vF vG : Nat, FieldValue f (.iterate m) x vF ∧ FieldValue f (.entry b lq mq) y vG ∧
        FormHolds f (distinctForm (.iterate m) (.entry b lq mq)) x y vF vG := by
  have hmono := (selected_threshold_admissible f B hf).1
  have hinfl : ∀ n, n ≤ f n := control_self_le f (selected_threshold_admissible f B hf).2
  refine ⟨peelTail B lq mq m,fun x y hx hxy => ?_⟩
  obtain ⟨i,hi,hye,hval⟩ := peeled_value f B hf b lq mq hG m y (hx.trans hxy.le)
  refine ⟨f^[m] x,_,rfl,hval,?_⟩
  rw [distinctForm]
  apply comparison_lt
  calc f^[m] x < f^[m] y := hmono.iterate m hxy
    _ ≤ f^[m] (entryNormAt f (countInitial lq.1.repr y) i) := (hmono.iterate m).monotone hye
    _ ≤ f^[b + m] (entryNormAt f (countInitial lq.1.repr y) i) := by
      rw [Function.iterate_add_apply]
      exact iterate_self_le hinfl b _

theorem distinct_entry_iterate (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (a : Nat) (lp mp : NONote) (n : Nat) (hF : LongField (.entry a lp mp)) :
    ∃ T : Nat, ∀ x y : Nat, T ≤ x → x < y →
      ∃ vF vG : Nat, FieldValue f (.entry a lp mp) x vF ∧ FieldValue f (.iterate n) y vG ∧
        FormHolds f (distinctForm (.entry a lp mp) (.iterate n)) x y vF vG := by
  have hmono := (selected_threshold_admissible f B hf).1
  refine ⟨max (peelTail B lp mp 0) (peelTail B lp mp (n - a)),fun x y hx hxy => ?_⟩
  by_cases hna : n ≤ a
  · obtain ⟨i,-,-,hval⟩ := peeled_value f B hf a lp mp hF 0 x ((le_max_left _ _).trans hx)
    obtain ⟨k,hk,-⟩ := hval
    refine ⟨f^[a] (entryNormAt f (countInitial lp.1.repr x) k),f^[n] y,⟨k,hk,rfl⟩,rfl,?_⟩
    rw [distinctForm,if_pos hna]
    refine ⟨f^[a - n] (entryNormAt f (countInitial lp.1.repr x) k),⟨k,hk,rfl⟩,?_⟩
    have hv : f^[a] (entryNormAt f (countInitial lp.1.repr x) k) =
        f^[n] (f^[a - n] (entryNormAt f (countInitial lp.1.repr x) k)) := by
      rw [← Function.iterate_add_apply,Nat.add_sub_cancel' hna]
    rw [hv]
    exact rows_exact (f^[n]) (hmono.iterate n) y _
  · obtain ⟨i,hi,-,hval⟩ := peeled_value f B hf a lp mp hF (n - a) x ((le_max_right _ _).trans hx)
    rw [Nat.add_sub_cancel' (Nat.le_of_not_le hna)] at hval
    refine ⟨_,f^[n] y,hval,rfl,?_⟩
    rw [distinctForm,if_neg hna]
    exact ⟨entryNormAt f (countInitial lp.1.repr x) i,⟨i,hi,rfl⟩,
      rows_exact (f^[n]) (hmono.iterate n) y _⟩

theorem distinct_entry_entry (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (a : Nat) (lp mp : NONote) (b : Nat) (lq mq : NONote)
    (hF : LongField (.entry a lp mp)) (hG : LongField (.entry b lq mq)) :
    ∃ T : Nat, ∀ x y : Nat, T ≤ x → x < y →
      ∃ vF vG : Nat, FieldValue f (.entry a lp mp) x vF ∧ FieldValue f (.entry b lq mq) y vG ∧
        FormHolds f (distinctForm (.entry a lp mp) (.entry b lq mq)) x y vF vG := by
  have hmono := (selected_threshold_admissible f B hf).1
  have hform := distinctForm_entry_entry a b lp mp lq mq
  have hP := peeled_proper a lp mp hF (b - a)
  have hQ := peeled_proper b lq mq hG (a - b)
  obtain ⟨mp',hmp'⟩ : ∃ m : NONote, m = mp + omegaMultiple (b - a) := ⟨_,rfl⟩
  obtain ⟨mq',hmq'⟩ : ∃ m : NONote, m = mq + omegaMultiple (a - b) := ⟨_,rfl⟩
  rw [← hmp',← hmq'] at hform
  rw [← hmp'] at hP
  rw [← hmq'] at hQ
  have hF' := hF
  have hG' := hG
  obtain ⟨hlpl,-,-,-⟩ := hF'
  obtain ⟨hlql,-,-,-⟩ := hG'
  have hlpE := normalRepresentationSound lp
  have hlqE := normalRepresentationSound lq
  have hdp : (lp - mp').1.repr = lp.1.repr - mp'.1.repr := note_sub_repr lp mp'
  have hdq : (lq - mq').1.repr = lq.1.repr - mq'.1.repr := note_sub_repr lq mq'
  have hQsum : mq'.1.repr + (lq - mq').1.repr = lq.1.repr := by
    rw [hdq]
    exact Ordinal.add_sub_cancel_of_le hQ.2.le
  have hdql : Order.IsSuccLimit (lq - mq').1.repr := by
    rw [hdq]
    exact Ordinal.isSuccLimit_sub hlql.isSuccPrelimit hQ.2
  refine ⟨max (max (peelTail B lp mp (b - a)) (peelTail B lq mq (a - b)))
    (max (inverseTableTail lp mp' mq' (lq - mq') B)
      (gapInputTail lq.1.repr mq'.1.repr lp.1.repr mp'.1.repr 0)),fun x y hx hxy => ?_⟩
  obtain ⟨hxP,-,hxI,hxG⟩ := tail_four _ _ _ _ x hx
  obtain ⟨-,hyQ,hyI,hyG⟩ := tail_four _ _ _ _ y (hx.trans hxy.le)
  obtain ⟨iP,hiP,-,hvalP⟩ := peeled_value f B hf a lp mp hF (b - a) x hxP
  obtain ⟨iQ,hiQ,-,hvalQ⟩ := peeled_value f B hf b lq mq hG (a - b) y hyQ
  rw [← hmp'] at hiP
  rw [← hmq'] at hiQ
  rw [← peel_exponent a b] at hvalQ
  refine ⟨_,_,hvalP,hvalQ,?_⟩
  rw [hform]
  have hcomp := NONote.cmp_compares (lq - mq') (lp - mp')
  by_cases hc : NONote.cmp (lq - mq') (lp - mp') = Ordering.lt
  · rw [if_pos hc]
    rw [hc] at hcomp
    have hlt : (lq - mq').1.repr < (lp - mp').1.repr := hcomp
    obtain ⟨hmk,hklam,i,j,p,q,lo,mid,hi',hi,hxh,hh,hj,hp',hq',hpij,hcont,-,-,-,-,-,-,hrows,-⟩ :=
      actualInverseTable f B hf lp mp' mq' (lq - mq') hlpl hP.1 hQ.1 hdql hP.2
        (by rw [← hdp]; exact hlt) x y hxI hyI
    rw [hQsum] at hq' hrows
    have ep := firstEntry_unique f _ _ p iP hp' hiP
    have eq' := firstEntry_unique f _ _ q iQ hq' hiQ
    rw [ep,eq'] at hrows
    refine ⟨entryNormAt f (countInitial lp.1.repr x) i,⟨i,?_,rfl⟩,
      rows_strictMono (f^[a + (b - a)]) (hmono.iterate _) _ _ _ _ _ hrows⟩
    rw [note_add_repr]
    exact hi
  · rw [if_neg hc]
    have hle : (lp - mp').1.repr ≤ (lq - mq').1.repr := by
      cases hcase : NONote.cmp (lq - mq') (lp - mp') with
      | lt => exact absurd hcase hc
      | eq =>
        rw [hcase] at hcomp
        have he : lq - mq' = lp - mp' := hcomp
        rw [he]
      | gt =>
        rw [hcase] at hcomp
        have hlt : (lp - mp').1.repr < (lq - mq').1.repr := hcomp
        exact hlt.le
    have hlt := inverse_input_comparison f B hf lq.1.repr mq'.1.repr lp.1.repr mp'.1.repr hlqE hlpE
      hlql hlpl hQ.1 hP.1 hQ.2 hP.2 (by rw [← hdp,← hdq]; exact hle) y x iQ iP hyG hxG hxy hiQ hiP
    exact comparison_lt ((hmono.iterate _) hlt)

theorem distinctInputForm : DistinctInputForm := by
  intro f B hf F G hF hG
  have hmono := (selected_threshold_admissible f B hf).1
  have hinfl : ∀ n, n ≤ f n := control_self_le f (selected_threshold_admissible f B hf).2
  cases F with
  | iterate m =>
    cases G with
    | iterate n => exact distinct_iterate_iterate f hmono hinfl m n
    | entry b lq mq => exact distinct_iterate_entry f B hf m b lq mq hG
  | entry a lp mp =>
    cases G with
    | iterate n => exact distinct_entry_iterate f B hf a lp mp n hF
    | entry b lq mq => exact distinct_entry_entry f B hf a lp mp b lq mq hF hG

/-! The branch with identified coordinates. -/

theorem same_iterate_entry (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m b : Nat) (lq mq : NONote) (hG : LongField (.entry b lq mq)) :
    ∃ T : Nat, ∀ x : Nat, T ≤ x → ∃ e : Nat,
      FieldValue f (.entry b lq mq) x (f^[b + (m + 1)] e) ∧ f^[m] x < f^[b + (m + 1)] e := by
  have hmono := (selected_threshold_admissible f B hf).1
  have hinfl : ∀ n, n ≤ f n := control_self_le f (selected_threshold_admissible f B hf).2
  refine ⟨peelTail B lq mq (m + 1),fun x hx => ?_⟩
  obtain ⟨i,-,hxe,hval⟩ := peeled_value f B hf b lq mq hG (m + 1) x hx
  refine ⟨_,hval,?_⟩
  calc f^[m] x < f^[m + 1] x := iterate_exponent_strict f (selected_strict f B hf) x (Nat.lt_succ_self m)
    _ ≤ f^[m + 1] (entryNormAt f (countInitial lq.1.repr x) i) := (hmono.iterate (m + 1)).monotone hxe
    _ ≤ f^[b + (m + 1)] (entryNormAt f (countInitial lq.1.repr x) i) := by
      rw [Function.iterate_add_apply f b (m + 1)]
      exact iterate_self_le hinfl b _

theorem same_entry_entry (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (a : Nat) (lp mp : NONote) (b : Nat) (lq mq : NONote)
    (hF : LongField (.entry a lp mp)) (hG : LongField (.entry b lq mq)) :
    ∃ T : Nat, ∀ x : Nat, T ≤ x →
      ∃ vF vG : Nat, FieldValue f (.entry a lp mp) x vF ∧ FieldValue f (.entry b lq mq) x vG ∧
        numericalComparison vF vG = sameForm (.entry a lp mp) (.entry b lq mq) := by
  have hmono := (selected_threshold_admissible f B hf).1
  have hform := sameForm_entry_entry a b lp mp lq mq
  have hP := peeled_proper a lp mp hF (b - a)
  have hQ := peeled_proper b lq mq hG (a - b)
  obtain ⟨mp',hmp'⟩ : ∃ m : NONote, m = mp + omegaMultiple (b - a) := ⟨_,rfl⟩
  obtain ⟨mq',hmq'⟩ : ∃ m : NONote, m = mq + omegaMultiple (a - b) := ⟨_,rfl⟩
  rw [← hmp',← hmq'] at hform
  rw [← hmp'] at hP
  rw [← hmq'] at hQ
  have hF' := hF
  have hG' := hG
  obtain ⟨hlpl,-,-,-⟩ := hF'
  obtain ⟨hlql,-,-,-⟩ := hG'
  have hlpE := normalRepresentationSound lp
  have hlqE := normalRepresentationSound lq
  have hdp : (lp - mp').1.repr = lp.1.repr - mp'.1.repr := note_sub_repr lp mp'
  have hdq : (lq - mq').1.repr = lq.1.repr - mq'.1.repr := note_sub_repr lq mq'
  have hPsum : mp'.1.repr + (lp - mp').1.repr = lp.1.repr := by
    rw [hdp]
    exact Ordinal.add_sub_cancel_of_le hP.2.le
  have hQsum : mq'.1.repr + (lq - mq').1.repr = lq.1.repr := by
    rw [hdq]
    exact Ordinal.add_sub_cancel_of_le hQ.2.le
  have hdpl : Order.IsSuccLimit (lp - mp').1.repr := by
    rw [hdp]
    exact Ordinal.isSuccLimit_sub hlpl.isSuccPrelimit hP.2
  refine ⟨max (max (peelTail B lp mp (b - a)) (peelTail B lq mq (a - b)))
    (max (max (gapInputTail lq.1.repr mq'.1.repr lp.1.repr mp'.1.repr 0)
      (gapInputTail lp.1.repr mp'.1.repr lq.1.repr mq'.1.repr 0))
      (equalGapCertificateTailCode (rawNoteEncode mp'.1) (rawNoteEncode mq'.1)
        (rawNoteEncode (lp - mp').1) B)),fun x hx => ?_⟩
  obtain ⟨hxP,hxQ,hxG1,hxG2,hxE⟩ := tail_five _ _ _ _ _ x hx
  obtain ⟨iP,hiP,-,hvalP⟩ := peeled_value f B hf a lp mp hF (b - a) x hxP
  obtain ⟨iQ,hiQ,-,hvalQ⟩ := peeled_value f B hf b lq mq hG (a - b) x hxQ
  rw [← hmp'] at hiP
  rw [← hmq'] at hiQ
  rw [← peel_exponent a b] at hvalQ
  refine ⟨_,_,hvalP,hvalQ,?_⟩
  rw [hform]
  have hcomp := NONote.cmp_compares (lp - mp') (lq - mq')
  by_cases h1 : NONote.cmp (lp - mp') (lq - mq') = Ordering.lt
  · rw [if_pos h1]
    rw [h1] at hcomp
    have hlt : (lp - mp').1.repr < (lq - mq').1.repr := hcomp
    obtain ⟨i,j,hi,hj,-,hval⟩ :=
      (gapInputComparison f B hf lq.1.repr mq'.1.repr lp.1.repr mp'.1.repr hlqE hlpE hlql hlpl
        hQ.1 hP.1 hQ.2 hP.2).1 (by rw [← hdp,← hdq]; exact hlt) x hxG1
    have ei := firstEntry_unique f _ _ i iQ hi hiQ
    have ej := firstEntry_unique f _ _ j iP hj hiP
    rw [ei,ej] at hval
    exact comparison_lt ((hmono.iterate _) hval)
  · rw [if_neg h1]
    by_cases h2 : NONote.cmp (lp - mp') (lq - mq') = Ordering.gt
    · rw [if_pos h2]
      rw [h2] at hcomp
      have hlt : (lq - mq').1.repr < (lp - mp').1.repr := hcomp
      obtain ⟨i,j,hi,hj,-,hval⟩ :=
        (gapInputComparison f B hf lp.1.repr mp'.1.repr lq.1.repr mq'.1.repr hlpE hlqE hlpl hlql
          hP.1 hQ.1 hP.2 hQ.2).1 (by rw [← hdp,← hdq]; exact hlt) x hxG2
      have ei := firstEntry_unique f _ _ i iP hi hiP
      have ej := firstEntry_unique f _ _ j iQ hj hiQ
      rw [ei,ej] at hval
      exact comparison_gt ((hmono.iterate _) hval)
    · rw [if_neg h2]
      have hdeq : lp - mp' = lq - mq' := by
        cases hcase : NONote.cmp (lp - mp') (lq - mq') with
        | lt => exact absurd hcase h1
        | eq =>
          rw [hcase] at hcomp
          exact hcomp
        | gt => exact absurd hcase h2
      have hQsum' : mq'.1.repr + (lp - mp').1.repr = lq.1.repr := by
        rw [hdeq]
        exact hQsum
      obtain ⟨tau,sigma,htau,hsigma,hs0,hs1,hs2⟩ :=
        equalGapSourceTail mp' mq' (lp - mp') hP.1 hQ.1 hdpl f B hf x hxE
      rw [hPsum] at htau hs0 hs1 hs2
      rw [hQsum'] at hsigma hs0 hs1 hs2
      have et := firstEntry_unique f _ _ tau iP htau hiP
      have es := firstEntry_unique f _ _ sigma iQ hsigma hiQ
      rw [et,es] at hs0 hs1 hs2
      rcases sign_cases _ (equalGapCertificateEffective.2.2 (rawNoteEncode mp'.1)
        (rawNoteEncode mq'.1) (rawNoteEncode (lp - mp').1)) with h0 | h0 | h0
      · rw [h0]
        exact comparison_lt ((hmono.iterate _) (hs0 h0))
      · rw [h0,hs1 h0]
        exact comparison_eq _
      · rw [h0]
        exact comparison_gt ((hmono.iterate _) (hs2 h0))

theorem equalInputForm : EqualInputForm := by
  intro f B hf F G hF hG
  cases F with
  | iterate m =>
    cases G with
    | iterate n =>
      refine ⟨0,fun x _ => ⟨f^[m] x,f^[n] x,rfl,rfl,?_⟩⟩
      exact comparison_strictMono (fun i : Nat => f^[i] x)
        (iterate_exponent_strict f (selected_strict f B hf) x) m n
    | entry b lq mq =>
      obtain ⟨T,hT⟩ := same_iterate_entry f B hf m b lq mq hG
      refine ⟨T,fun x hx => ?_⟩
      obtain ⟨e,hval,hlt⟩ := hT x hx
      exact ⟨f^[m] x,_,rfl,hval,comparison_lt hlt⟩
  | entry a lp mp =>
    cases G with
    | iterate n =>
      obtain ⟨T,hT⟩ := same_iterate_entry f B hf n a lp mp hF
      refine ⟨T,fun x hx => ?_⟩
      obtain ⟨e,hval,hlt⟩ := hT x hx
      exact ⟨_,f^[n] x,hval,rfl,comparison_gt hlt⟩
    | entry b lq mq => exact same_entry_entry f B hf a lp mp b lq mq hF hG

/-! Remaining clauses. -/

theorem shortEntryIterate : ShortEntryIterate := by
  intro f B hf mu k x hk hE hmu hx
  have hkl : Order.IsSuccLimit (mu + Ordinal.omega0 * (k : Ordinal)) :=
    Ordinal.isSuccLimit_add _ (omega_multiple_limit k hk)
  have hmk : mu < mu + Ordinal.omega0 * (k : Ordinal) := by
    simpa only [add_zero] using (add_lt_add_iff_left mu).mpr (omega_multiple_limit k hk).pos
  obtain ⟨i,hi,hn,hshort,-⟩ := entryResidues f B hf 1 (mu + Ordinal.omega0 * (k : Ordinal)) mu x
    (by decide) hE hkl hmu hmk hx
  have hik : i = k := hshort k hk rfl
  rw [hik] at hi hn
  exact ⟨hi,hn⟩

theorem fieldValueUnique : FieldValueUnique := by
  intro f F u v v' hv hv'
  cases F with
  | iterate a =>
    have h1 : v = f^[a] u := hv
    have h2 : v' = f^[a] u := hv'
    rw [h1,h2]
  | entry a lam mu =>
    obtain ⟨i,hi,h1⟩ := hv
    obtain ⟨j,hj,h2⟩ := hv'
    have e := firstEntry_unique f _ _ i j hi hj
    rw [h1,h2,e]

theorem formWellFormed : FormWellFormed := by
  intro F G hF hG sign H hform
  cases F with
  | iterate m =>
    cases G with
    | iterate n =>
      by_cases hmn : m ≤ n
      · rw [distinctForm,if_pos hmn] at hform
        cases hform
      · rw [distinctForm,if_neg hmn] at hform
        cases hform
        exact ⟨by decide,trivial⟩
    | entry b lq mq =>
      rw [distinctForm] at hform
      cases hform
  | entry a lp mp =>
    have hF' := hF
    obtain ⟨hlpl,hmp,hmpl,-⟩ := hF'
    cases G with
    | iterate n =>
      by_cases hna : n ≤ a
      · rw [distinctForm,if_pos hna] at hform
        cases hform
        exact ⟨by decide,hlpl,hmp,hmpl⟩
      · rw [distinctForm,if_neg hna] at hform
        cases hform
        have hp := peeled_proper a lp mp hF (n - a)
        exact ⟨by decide,hlpl,hp.1,hp.2⟩
    | entry b lq mq =>
      rw [distinctForm_entry_entry] at hform
      have hP := peeled_proper a lp mp hF (b - a)
      have hQ := peeled_proper b lq mq hG (a - b)
      have hcomp := NONote.cmp_compares (lq - (mq + omegaMultiple (a - b)))
        (lp - (mp + omegaMultiple (b - a)))
      by_cases hc : NONote.cmp (lq - (mq + omegaMultiple (a - b)))
          (lp - (mp + omegaMultiple (b - a))) = Ordering.lt
      · rw [if_pos hc] at hform
        cases hform
        rw [hc] at hcomp
        have hlt : (lq - (mq + omegaMultiple (a - b))).1.repr <
            (lp - (mp + omegaMultiple (b - a))).1.repr := hcomp
        have hG' := hG
        obtain ⟨hlql,-,-,-⟩ := hG'
        have hdql : Order.IsSuccLimit (lq - (mq + omegaMultiple (a - b))).1.repr := by
          rw [note_sub_repr]
          exact Ordinal.isSuccLimit_sub hlql.isSuccPrelimit hQ.2
        rw [note_sub_repr lp] at hlt
        refine ⟨equalGapCertificateEffective.2.2 _ _ _,hlpl,?_,?_⟩
        · rw [note_add_repr]
          exact Or.inr (Ordinal.isSuccLimit_add _ hdql)
        · rw [note_add_repr]
          exact Ordinal.lt_sub.mp hlt
      · rw [if_neg hc] at hform
        cases hform

theorem fullFieldComparison : FullFieldComparison :=
  ⟨shortEntryIterate,fieldValueUnique,formWellFormed,distinctInputForm,equalInputForm⟩

end LogicLineages.PermittedControl.FieldComparison
