module
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceTargets
public import LogicLineages.OrdinalComparison.CollectedPositiveProof
public import Mathlib.Data.List.Pairwise
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem entries_value (sign : Int) (tags : CollectedPositiveTags) (x : Nat) :
    actualSignedCollectedValue (signedCollectedEntries sign tags) x=
      sign*(actualCollectedTagsEval tags x : Int) := by
  cases tags with
  | nil => simp [signedCollectedEntries,actualSignedCollectedValue,actualCollectedTagsEval]
  | cons rho A a rest =>
    have ih := entries_value sign rest x
    simp only [signedCollectedEntries,actualSignedCollectedValue,List.map_cons,List.sum_cons,
      actualCollectedTagsEval,Nat.cast_add,Nat.cast_mul] at ih ⊢
    rw [ih]
    ring
termination_by tags

private theorem difference_value (left right : CollectedPositiveTags) (x : Nat) :
    actualSignedCollectedValue (signedCollectedDifference left right) x=
      (actualCollectedTagsEval left x : Int)-(actualCollectedTagsEval right x : Int) := by
  cases left with
  | nil => simp [signedCollectedDifference,entries_value,actualCollectedTagsEval]
  | cons rho A a rest =>
    cases right with
    | nil => simp [signedCollectedDifference,entries_value,actualCollectedTagsEval]
    | cons sigma B b tail =>
      by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
      · rw [signedCollectedDifference,if_pos hl]
        have ih := difference_value rest (.cons sigma B b tail) x
        simp only [actualSignedCollectedValue,List.map_cons,List.sum_cons] at ih ⊢
        rw [ih]
        simp only [actualCollectedTagsEval,Nat.cast_add,Nat.cast_mul]
        ring
      · by_cases he : collectedTagKey rho A=collectedTagKey sigma B
        · rcases (collectedPositiveTagIdentity rho sigma A B).mp he with ⟨hr,hA⟩
          subst sigma; subst B
          by_cases hab : a=b
          · subst b
            rw [signedCollectedDifference,if_neg hl,if_pos rfl,if_pos rfl]
            rw [difference_value rest tail x]
            simp only [actualCollectedTagsEval,Nat.cast_add,Nat.cast_mul]
            ring
          · rw [signedCollectedDifference,if_neg hl,if_pos rfl,if_neg hab]
            have ih := difference_value rest tail x
            simp only [actualSignedCollectedValue,List.map_cons,List.sum_cons] at ih ⊢
            rw [ih]
            simp only [actualCollectedTagsEval,Nat.cast_add,Nat.cast_mul]
            ring
        · rw [signedCollectedDifference,if_neg hl,if_neg he]
          have ih := difference_value (.cons rho A a rest) tail x
          simp only [actualSignedCollectedValue,List.map_cons,List.sum_cons] at ih ⊢
          rw [ih]
          simp only [actualCollectedTagsEval,Nat.cast_add,Nat.cast_mul]
          ring
termination_by collectedDictionaryLength left+collectedDictionaryLength right
decreasing_by
  all_goals simp_wf
  all_goals simp_all [collectedDictionaryLength]
  all_goals omega

private theorem entries_provenance (sign : Int) (tags : CollectedPositiveTags)
    (entry : (NONote × CollectedPositiveNF) × Int) (h : entry∈signedCollectedEntries sign tags) :
    entry.1∈collectedDirectTags tags := by
  cases tags with
  | nil => simp [signedCollectedEntries] at h
  | cons rho A a rest =>
    rcases List.mem_cons.mp h with h | h
    · subst entry; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (entries_provenance sign rest entry h)
termination_by tags

private theorem difference_provenance (left right : CollectedPositiveTags)
    (entry : (NONote × CollectedPositiveNF) × Int) (h : entry∈signedCollectedDifference left right) :
    entry.1∈collectedDirectTags left ∨ entry.1∈collectedDirectTags right := by
  cases left with
  | nil =>
    rw [signedCollectedDifference] at h
    exact Or.inr (entries_provenance (-1) right entry h)
  | cons rho A a rest =>
    cases right with
    | nil =>
      rw [signedCollectedDifference] at h <;> try { intro hn; cases hn }
      exact Or.inl (entries_provenance 1 (.cons rho A a rest) entry h)
    | cons sigma B b tail =>
      rw [signedCollectedDifference] at h
      split at h
      · rcases List.mem_cons.mp h with h | h
        · subst entry; exact Or.inl List.mem_cons_self
        · rcases difference_provenance rest (.cons sigma B b tail) entry h with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
      · split at h
        · split at h
          · rcases difference_provenance rest tail entry h with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · exact Or.inr (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.mp h with h | h
            · subst entry; exact Or.inl List.mem_cons_self
            · rcases difference_provenance rest tail entry h with h | h
              · exact Or.inl (List.mem_cons_of_mem _ h)
              · exact Or.inr (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with h | h
          · subst entry; exact Or.inr List.mem_cons_self
          · rcases difference_provenance (.cons rho A a rest) tail entry h with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem _ h)
termination_by collectedDictionaryLength left+collectedDictionaryLength right
decreasing_by
  all_goals simp_wf
  all_goals simp_all [collectedDictionaryLength]
  all_goals omega

private theorem direct_above (k : Nat) (tags : CollectedPositiveTags)
    (hk : collectedTagsKeysAbove k tags) (rho : NONote) (A : CollectedPositiveNF)
    (hm : (rho,A)∈collectedDirectTags tags) : k<collectedTagKey rho A := by
  cases tags with
  | nil => simp [collectedDirectTags] at hm
  | cons sigma B b rest =>
    rcases List.mem_cons.mp hm with h | h
    · cases h; exact hk.1
    · exact direct_above k rest hk.2 rho A h
termination_by tags

private theorem signed_cons_valid (rho : NONote) (A : CollectedPositiveNF) (z : Int)
    (row : SignedCollectedRow) (hz : z≠0) (hl : Order.IsSuccLimit rho.1.repr)
    (he : rho.1.repr<epsilonZero) (hA : CollectedPositiveValid A)
    (ho : collectedPositiveSupport A=true) (hr : SignedCollectedValid row)
    (hk : ∀ entry∈row, collectedTagKey rho A<collectedTagKey entry.1.1 entry.1.2) :
    SignedCollectedValid (((rho,A),z)::row) := by
  refine ⟨List.pairwise_cons.mpr ⟨hk,hr.1⟩,?_⟩
  intro entry hm
  rcases List.mem_cons.mp hm with h | h
  · subst entry; exact ⟨hz,hl,he,hA,ho⟩
  · exact hr.2 entry h

private theorem entries_valid (sign : Int) (hs : sign≠0) (tags : CollectedPositiveTags)
    (hv : CollectedTagsValid tags) : SignedCollectedValid (signedCollectedEntries sign tags) := by
  cases tags with
  | nil => exact ⟨by simp [signedCollectedEntries],by simp [signedCollectedEntries]⟩
  | cons rho A a rest =>
    apply signed_cons_valid rho A (sign*(a : Int)) _
      (mul_ne_zero hs (by exact_mod_cast Nat.ne_of_gt hv.2.2.2.2.1))
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 (entries_valid sign hs rest hv.2.2.2.2.2.2)
    intro entry hm
    exact direct_above _ rest hv.2.2.2.2.2.1 entry.1.1 entry.1.2
      (entries_provenance sign rest entry hm)
termination_by tags

private theorem difference_valid (left right : CollectedPositiveTags)
    (hv : CollectedTagsValid left) (hw : CollectedTagsValid right) :
    SignedCollectedValid (signedCollectedDifference left right) := by
  cases left with
  | nil =>
    rw [signedCollectedDifference]
    exact entries_valid (-1) (by decide) right hw
  | cons rho A a rest =>
    cases right with
    | nil =>
      rw [signedCollectedDifference] <;> try { intro hn; cases hn }
      exact entries_valid 1 (by decide) (.cons rho A a rest) hv
    | cons sigma B b tail =>
      by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
      · rw [signedCollectedDifference,if_pos hl]
        apply signed_cons_valid rho A (a : Int) _
          (by exact_mod_cast Nat.ne_of_gt hv.2.2.2.2.1) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
          (difference_valid rest (.cons sigma B b tail) hv.2.2.2.2.2.2 hw)
        intro entry hm
        rcases difference_provenance rest (.cons sigma B b tail) entry hm with h | h
        · exact direct_above _ rest hv.2.2.2.2.2.1 entry.1.1 entry.1.2 h
        · rcases List.mem_cons.mp h with h | h
          · rw [h]; exact hl
          · exact hl.trans (direct_above _ tail hw.2.2.2.2.2.1 entry.1.1 entry.1.2 h)
      · by_cases he : collectedTagKey rho A=collectedTagKey sigma B
        · rcases (collectedPositiveTagIdentity rho sigma A B).mp he with ⟨hr,hA⟩
          subst sigma; subst B
          by_cases hab : a=b
          · rw [signedCollectedDifference,if_neg hl,if_pos rfl,if_pos hab]
            exact difference_valid rest tail hv.2.2.2.2.2.2 hw.2.2.2.2.2.2
          · rw [signedCollectedDifference,if_neg hl,if_pos rfl,if_neg hab]
            apply signed_cons_valid rho A ((a : Int)-(b : Int)) _
              (sub_ne_zero.mpr (by exact_mod_cast hab)) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
              (difference_valid rest tail hv.2.2.2.2.2.2 hw.2.2.2.2.2.2)
            intro entry hm
            rcases difference_provenance rest tail entry hm with h | h
            · exact direct_above _ rest hv.2.2.2.2.2.1 entry.1.1 entry.1.2 h
            · exact direct_above _ tail hw.2.2.2.2.2.1 entry.1.1 entry.1.2 h
        · have hlt : collectedTagKey sigma B<collectedTagKey rho A := by omega
          rw [signedCollectedDifference,if_neg hl,if_neg he]
          apply signed_cons_valid sigma B (-(b : Int)) _
            (neg_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hw.2.2.2.2.1))
            hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
            (difference_valid (.cons rho A a rest) tail hv hw.2.2.2.2.2.2)
          intro entry hm
          rcases difference_provenance (.cons rho A a rest) tail entry hm with h | h
          · rcases List.mem_cons.mp h with h | h
            · rw [h]; exact hlt
            · exact hlt.trans (direct_above _ rest hv.2.2.2.2.2.1 entry.1.1 entry.1.2 h)
          · exact direct_above _ tail hw.2.2.2.2.2.1 entry.1.1 entry.1.2 h
termination_by collectedDictionaryLength left+collectedDictionaryLength right
decreasing_by
  all_goals simp_wf
  all_goals simp_all [collectedDictionaryLength]
  all_goals omega

theorem signedCollectedDifferenceValid : Targets.SignedCollectedDifferenceValid := by
  intro left right hv hw
  exact ⟨difference_valid left right hv hw,difference_provenance left right⟩

private theorem difference_empty (left right : CollectedPositiveTags) :
    signedCollectedDifference left right=[] ↔ left=right := by
  cases left with
  | nil => cases right <;> simp [signedCollectedDifference,signedCollectedEntries]
  | cons rho A a rest =>
    cases right with
    | nil => simp [signedCollectedDifference,signedCollectedEntries]
    | cons sigma B b tail =>
      by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
      · have hne : CollectedPositiveTags.cons rho A a rest≠.cons sigma B b tail := by
          intro h; cases h; exact (Nat.lt_irrefl _ hl)
        simp [signedCollectedDifference,hl,hne]
      · by_cases he : collectedTagKey rho A=collectedTagKey sigma B
        · rcases (collectedPositiveTagIdentity rho sigma A B).mp he with ⟨hr,hA⟩
          subst sigma; subst B
          by_cases hab : a=b
          · subst b
            rw [signedCollectedDifference,if_neg hl,if_pos rfl,if_pos rfl]
            simpa only [CollectedPositiveTags.cons.injEq,true_and] using difference_empty rest tail
          · have hne : CollectedPositiveTags.cons rho A a rest≠.cons rho A b tail := by
              intro h; cases h; exact hab rfl
            simp [signedCollectedDifference,hl,hab,hne]
        · have hne : CollectedPositiveTags.cons rho A a rest≠.cons sigma B b tail := by
            intro h; cases h; exact he rfl
          simp [signedCollectedDifference,hl,he,hne]
termination_by collectedDictionaryLength left+collectedDictionaryLength right
decreasing_by
  all_goals simp_wf
  all_goals simp_all [collectedDictionaryLength]
  all_goals omega

theorem signedCollectedDifferenceValue : Targets.SignedCollectedDifferenceValue := difference_value

theorem signedCollectedDifferenceEmpty : Targets.SignedCollectedDifferenceEmpty := difference_empty

theorem signedCollectedNFRowValue : Targets.SignedCollectedNFRowValue := by
  intro A B x
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      dsimp only [signedCollectedNFRow]
      rw [signedCollectedDifferenceValue tags rest x]
      simp only [actualCollectedPositiveEval,Nat.cast_add,Nat.cast_mul]
      ring

end LogicLineages.OrdinalComparison
