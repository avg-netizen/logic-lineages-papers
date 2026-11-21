module
public import LogicLineages.PermittedControl.ShortFieldPreprocessingTargets
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.PermittedControl.FieldComparisonProof
import LogicLineages.PermittedControl.EntryLinearProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private theorem short_normalize_zero (a : Nat) (lam mu : NONote)
    (hp : ProperField (.entry a lam mu)) (hk : shortGapLength lam mu = 0) :
    LongField (.entry a lam mu) ∧ normalizeShortField (.entry a lam mu) = .entry a lam mu := by
  refine ⟨⟨hp.1,hp.2.1,hp.2.2,?_⟩,?_⟩
  · rintro ⟨k,hpos,heq⟩
    have h := (shortGapRecognition lam mu hp k hpos).2.2.mpr heq
    exact Nat.ne_of_gt hpos (h.symm.trans hk)
  · change (match (if shortGapLength lam mu = 0 then 0 else a + shortGapLength lam mu + 1) with
      | 0 => ValueField.entry a lam mu
      | n+1 => ValueField.iterate n) = .entry a lam mu
    rw [if_pos hk]

private theorem short_normalize_positive (a : Nat) (lam mu : NONote)
    (hk : 0 < shortGapLength lam mu) :
    normalizeShortField (.entry a lam mu) = .iterate (a + shortGapLength lam mu) := by
  change (match (if shortGapLength lam mu = 0 then 0 else a + shortGapLength lam mu + 1) with
    | 0 => ValueField.entry a lam mu
    | n+1 => ValueField.iterate n) = _
  rw [if_neg (Nat.ne_of_gt hk)]

theorem shortFieldNormalization : ShortFieldNormalization := by
  refine ⟨fun _ => rfl,?_,?_,?_⟩
  · intro a lam mu hp
    exact ⟨short_normalize_zero a lam mu hp,short_normalize_positive a lam mu⟩
  · intro F hp
    cases F with
    | iterate a => trivial
    | entry a lam mu =>
      rcases Nat.eq_zero_or_pos (shortGapLength lam mu) with hz | hpos
      · have h := short_normalize_zero a lam mu hp hz
        rw [h.2]
        exact h.1
      · rw [short_normalize_positive a lam mu hpos]
        trivial
  · intro f B hf F hp x v hx
    cases F with
    | iterate a => rfl
    | entry a lam mu =>
      rcases Nat.eq_zero_or_pos (shortGapLength lam mu) with hz | hpos
      · rw [(short_normalize_zero a lam mu hp hz).2]
      · let k := shortGapLength lam mu
        have hpos' : 0 < k := hpos
        have hends : lam.1.repr = mu.1.repr + Ordinal.omega0 * (k : Ordinal) :=
          (shortGapRecognition lam mu hp k hpos').2.2.mp rfl
        have htail : max (actualOrdinalNorm lam.1.repr)
            (max (actualOrdinalNorm mu.1.repr + 3) (max 1 B)) ≤ x :=
          ((shortFieldPreprocessingEffective.2.2.2.2 lam mu B).symm.trans_le hx)
        have hE := normalRepresentationSound lam
        rw [hends] at htail hE
        obtain ⟨hentry,hnorm⟩ := shortEntryIterate f B hf mu.1.repr k x hpos' hE hp.2.1 htail
        rw [← hends] at hentry hnorm
        rw [short_normalize_positive a lam mu hpos]
        change (∃ i : Nat, FirstEntry f (countInitial lam.1.repr x) mu.1.repr i ∧
          v = f^[a] (entryNormAt f (countInitial lam.1.repr x) i)) ↔ v = f^[a+k] x
        rw [Function.iterate_add_apply]
        constructor
        · rintro ⟨i,hi,hval⟩
          have hik := firstEntry_unique f _ _ i k hi hentry
          simpa only [hik,hnorm] using hval
        · intro hval
          exact ⟨k,hentry,by rw [hnorm]; exact hval⟩

theorem fullShortFieldPreprocessing : FullShortFieldPreprocessing :=
  ⟨shortGapRecognition,shortFieldPreprocessingEffective,shortFieldNormalization⟩

end LogicLineages.PermittedControl.FieldComparison
