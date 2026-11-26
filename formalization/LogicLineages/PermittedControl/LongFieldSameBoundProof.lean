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

private theorem long_same_iterate_entry (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m b : Nat) (lq mq : NONote) (hG : LongField (.entry b lq mq)) :
    ∀ x : Nat, longFieldSameBound B (.iterate m) (.entry b lq mq) ≤ x → ∃ e : Nat,
      FieldValue f (.entry b lq mq) x (f^[b + (m + 1)] e) ∧ f^[m] x < f^[b + (m + 1)] e := by
  have hmono := (selected_threshold_admissible f B hf).1
  have hinfl : ∀ n, n ≤ f n := control_self_le f (selected_threshold_admissible f B hf).2
  intro x hx
  change longFieldPeelBound B lq mq (m + 1) ≤ x at hx
  obtain ⟨i,-,hxe,hval⟩ := long_peeled_value f B hf b lq mq hG (m + 1) x hx
  refine ⟨_,hval,?_⟩
  calc f^[m] x < f^[m + 1] x := iterate_exponent_strict f (selected_strict f B hf) x (Nat.lt_succ_self m)
    _ ≤ f^[m + 1] (entryNormAt f (countInitial lq.1.repr x) i) := (hmono.iterate (m + 1)).monotone hxe
    _ ≤ f^[b + (m + 1)] (entryNormAt f (countInitial lq.1.repr x) i) := by
      rw [Function.iterate_add_apply f b (m + 1)]
      exact iterate_self_le hinfl b _

private theorem long_same_entry_entry (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (a : Nat) (lp mp : NONote) (b : Nat) (lq mq : NONote)
    (hF : LongField (.entry a lp mp)) (hG : LongField (.entry b lq mq)) :
    ∀ x : Nat, longFieldSameBound B (.entry a lp mp) (.entry b lq mq) ≤ x →
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
  intro x hbound
  have hx : max (max (longFieldPeelBound B lp mp (b - a)) (longFieldPeelBound B lq mq (a - b)))
    (max (max (gapInputTail lq.1.repr mq'.1.repr lp.1.repr mp'.1.repr 0)
      (gapInputTail lp.1.repr mp'.1.repr lq.1.repr mq'.1.repr 0))
      (equalGapCertificateTailCode (rawNoteEncode mp'.1) (rawNoteEncode mq'.1)
        (rawNoteEncode (lp - mp').1) B)) ≤ x := by
    rw [hmp',hmq']
    exact hbound
  obtain ⟨hxP,hxQ,hxG1,hxG2,hxE⟩ := tail_five _ _ _ _ _ x hx
  obtain ⟨iP,hiP,-,hvalP⟩ := long_peeled_value f B hf a lp mp hF (b - a) x hxP
  obtain ⟨iQ,hiQ,-,hvalQ⟩ := long_peeled_value f B hf b lq mq hG (a - b) x hxQ
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

theorem longFieldSameAtBound : LongFieldSameAtBound := by
  intro f B hf F G hF hG
  cases F with
  | iterate m =>
    cases G with
    | iterate n =>
      intro x _
      refine ⟨f^[m] x,f^[n] x,rfl,rfl,?_⟩
      exact comparison_strictMono (fun i : Nat => f^[i] x)
        (iterate_exponent_strict f (selected_strict f B hf) x) m n
    | entry b lq mq =>
      intro x hx
      obtain ⟨e,hval,hlt⟩ := long_same_iterate_entry f B hf m b lq mq hG x hx
      exact ⟨f^[m] x,_,rfl,hval,comparison_lt hlt⟩
  | entry a lp mp =>
    cases G with
    | iterate n =>
      intro x hx
      obtain ⟨e,hval,hlt⟩ := long_same_iterate_entry f B hf n a lp mp hF x hx
      exact ⟨_,f^[n] x,hval,rfl,comparison_gt hlt⟩
    | entry b lq mq => exact long_same_entry_entry f B hf a lp mp b lq mq hF hG

end LogicLineages.PermittedControl.FieldComparison
