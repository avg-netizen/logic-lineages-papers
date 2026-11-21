module
public import LogicLineages.PermittedControl.LongFieldEffectiveTailTargets
import LogicLineages.PermittedControl.FieldComparisonProof
import LogicLineages.PermittedControl.LongFieldPeeledValueProof
import LogicLineages.PermittedControl.FieldComparisonPeelProof
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.EntryLinearProof
import LogicLineages.PermittedControl.InverseTableProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/- The existing local witness argument, strengthened append-only to use the
named exact bound rather than existentially hiding its literal value. -/

private theorem long_distinct_iterate_iterate (f : Nat → Nat) (hmono : StrictMono f) (hinfl : ∀ n, n ≤ f n)
    (m n : Nat) :
    ∀ x y : Nat, 0 ≤ x → x < y →
      ∃ vF vG : Nat, FieldValue f (.iterate m) x vF ∧ FieldValue f (.iterate n) y vG ∧
        FormHolds f (distinctForm (.iterate m) (.iterate n)) x y vF vG := by
  intro x y _ hxy
  refine ⟨f^[m] x,f^[n] y,rfl,rfl,?_⟩
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

private theorem long_distinct_iterate_entry (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m b : Nat) (lq mq : NONote) (hG : LongField (.entry b lq mq)) :
    ∀ x y : Nat, longFieldDistinctBound B (.iterate m) (.entry b lq mq) ≤ x → x < y →
      ∃ vF vG : Nat, FieldValue f (.iterate m) x vF ∧ FieldValue f (.entry b lq mq) y vG ∧
        FormHolds f (distinctForm (.iterate m) (.entry b lq mq)) x y vF vG := by
  have hmono := (selected_threshold_admissible f B hf).1
  have hinfl : ∀ n, n ≤ f n := control_self_le f (selected_threshold_admissible f B hf).2
  intro x y hx hxy
  change longFieldPeelBound B lq mq m ≤ x at hx
  obtain ⟨i,hi,hye,hval⟩ := long_peeled_value f B hf b lq mq hG m y (hx.trans hxy.le)
  refine ⟨f^[m] x,_,rfl,hval,?_⟩
  rw [distinctForm]
  apply comparison_lt
  calc f^[m] x < f^[m] y := hmono.iterate m hxy
    _ ≤ f^[m] (entryNormAt f (countInitial lq.1.repr y) i) := (hmono.iterate m).monotone hye
    _ ≤ f^[b + m] (entryNormAt f (countInitial lq.1.repr y) i) := by
      rw [Function.iterate_add_apply]
      exact iterate_self_le hinfl b _

private theorem long_distinct_entry_iterate (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (a : Nat) (lp mp : NONote) (n : Nat) (hF : LongField (.entry a lp mp)) :
    ∀ x y : Nat, longFieldDistinctBound B (.entry a lp mp) (.iterate n) ≤ x → x < y →
      ∃ vF vG : Nat, FieldValue f (.entry a lp mp) x vF ∧ FieldValue f (.iterate n) y vG ∧
        FormHolds f (distinctForm (.entry a lp mp) (.iterate n)) x y vF vG := by
  have hmono := (selected_threshold_admissible f B hf).1
  intro x y hx hxy
  change max (longFieldPeelBound B lp mp 0) (longFieldPeelBound B lp mp (n - a)) ≤ x at hx
  by_cases hna : n ≤ a
  · obtain ⟨i,-,-,hval⟩ := long_peeled_value f B hf a lp mp hF 0 x ((le_max_left _ _).trans hx)
    obtain ⟨k,hk,-⟩ := hval
    refine ⟨f^[a] (entryNormAt f (countInitial lp.1.repr x) k),f^[n] y,⟨k,hk,rfl⟩,rfl,?_⟩
    rw [distinctForm,if_pos hna]
    refine ⟨f^[a - n] (entryNormAt f (countInitial lp.1.repr x) k),⟨k,hk,rfl⟩,?_⟩
    have hv : f^[a] (entryNormAt f (countInitial lp.1.repr x) k) =
        f^[n] (f^[a - n] (entryNormAt f (countInitial lp.1.repr x) k)) := by
      rw [← Function.iterate_add_apply,Nat.add_sub_cancel' hna]
    rw [hv]
    exact rows_exact (f^[n]) (hmono.iterate n) y _
  · obtain ⟨i,hi,-,hval⟩ := long_peeled_value f B hf a lp mp hF (n - a) x ((le_max_right _ _).trans hx)
    rw [Nat.add_sub_cancel' (Nat.le_of_not_le hna)] at hval
    refine ⟨_,f^[n] y,hval,rfl,?_⟩
    rw [distinctForm,if_neg hna]
    exact ⟨entryNormAt f (countInitial lp.1.repr x) i,⟨i,hi,rfl⟩,
      rows_exact (f^[n]) (hmono.iterate n) y _⟩

private theorem long_distinct_entry_entry (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (a : Nat) (lp mp : NONote) (b : Nat) (lq mq : NONote)
    (hF : LongField (.entry a lp mp)) (hG : LongField (.entry b lq mq)) :
    ∀ x y : Nat, longFieldDistinctBound B (.entry a lp mp) (.entry b lq mq) ≤ x → x < y →
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
  intro x y hbound hxy
  have hx : max (max (longFieldPeelBound B lp mp (b - a)) (longFieldPeelBound B lq mq (a - b)))
    (max (inverseTableTail lp mp' mq' (lq - mq') B)
      (gapInputTail lq.1.repr mq'.1.repr lp.1.repr mp'.1.repr 0)) ≤ x := by
    rw [hmp',hmq']
    exact hbound
  obtain ⟨hxP,-,hxI,hxG⟩ := tail_four _ _ _ _ x hx
  obtain ⟨-,hyQ,hyI,hyG⟩ := tail_four _ _ _ _ y (hx.trans hxy.le)
  obtain ⟨iP,hiP,-,hvalP⟩ := long_peeled_value f B hf a lp mp hF (b - a) x hxP
  obtain ⟨iQ,hiQ,-,hvalQ⟩ := long_peeled_value f B hf b lq mq hG (a - b) y hyQ
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

theorem longFieldDistinctAtBound : LongFieldDistinctAtBound := by
  intro f B hf F G hF hG
  have hmono := (selected_threshold_admissible f B hf).1
  have hinfl : ∀ n, n ≤ f n := control_self_le f (selected_threshold_admissible f B hf).2
  cases F with
  | iterate m =>
    cases G with
    | iterate n => exact long_distinct_iterate_iterate f hmono hinfl m n
    | entry b lq mq => exact long_distinct_iterate_entry f B hf m b lq mq hG
  | entry a lp mp =>
    cases G with
    | iterate n => exact long_distinct_entry_iterate f B hf a lp mp n hF
    | entry b lq mq => exact long_distinct_entry_entry f B hf a lp mp b lq mq hF hG

end LogicLineages.PermittedControl.FieldComparison
