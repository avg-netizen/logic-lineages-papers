module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatchingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatchingProof
open Source Source.SourceOpenedObservations FiniteObservationBits TypedExtraDownsets TypedObservationAccess FiniteOccurrenceMatching

theorem splitCalibration : FiniteOccurrenceMatchingTargets.SplitCalibration := by
  intro α xs kept removed
  simp only [splits,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨zs,hzs,k,hk,he⟩
    cases he
    simpa only [List.take_append_drop] using (List.mem_permutations.mp hzs).symm
  · intro h
    refine ⟨kept++removed,List.mem_permutations.mpr h.symm,kept.length,?_,?_⟩
    · simp only [List.mem_range,List.length_append]; omega
    · simp

theorem orderedSpec {α β : Type} (W : α → β → Bool) (xs : List α) (ys : List β) :
    orderedTest W xs ys=true ↔ List.Forall₂ (fun s t => W s t=true) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [orderedTest]
  | cons x xs ih => cases ys <;> simp [orderedTest,ih]

theorem weakSpec {α β : Type} (W : α → β → Bool) (xs : List α) (ys : List β) :
    weakTest W xs ys=true ↔ ∃ matched,ys.Perm matched ∧ List.Forall₂ (fun s t => W s t=true) xs matched := by
  simp only [weakTest,List.any_eq_true,orderedSpec,List.mem_permutations]
  exact ⟨fun ⟨zs,hz,hm⟩ => ⟨zs,hz.symm,hm⟩,fun ⟨zs,hz,hm⟩ => ⟨zs,hz.symm,hm⟩⟩

theorem replacementSpec {α β : Type} (S : α → β → Bool) (xs : List α) (ys : List β) :
    replacementTest S xs ys=true ↔ ∀ t ∈ ys,∃ s ∈ xs,S s t=true := by
  simp only [replacementTest,List.all_eq_true,List.any_eq_true]

theorem strictSpec {α β : Type} (W S : α → β → Bool) (xs : List α) (ys : List β) :
    strictTest W S xs ys=true ↔ ∃ kept removed retained inserted,
      xs.Perm (kept++removed) ∧ ys.Perm (retained++inserted) ∧ removed≠[] ∧
      List.Forall₂ (fun s t => W s t=true) kept retained ∧ (∀ t ∈ inserted,∃ s ∈ removed,S s t=true) := by
  simp only [strictTest,List.any_eq_true]
  constructor
  · rintro ⟨⟨kept,removed⟩,hs,⟨⟨retained,inserted⟩,ht,h⟩⟩
    obtain ⟨h12,h3⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h12
    have hn : removed≠[] := by intro he; subst removed; simp at h1
    exact ⟨kept,removed,retained,inserted,(splitCalibration α xs kept removed).mp hs,
      (splitCalibration β ys retained inserted).mp ht,hn,(orderedSpec W kept retained).mp h2,
      (replacementSpec S removed inserted).mp h3⟩
  · rintro ⟨kept,removed,retained,inserted,hs,ht,hn,hw,hr⟩
    refine ⟨(kept,removed),(splitCalibration α xs kept removed).mpr hs,
      (retained,inserted),(splitCalibration β ys retained inserted).mpr ht,?_⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨?_,(orderedSpec W kept retained).mpr hw⟩,(replacementSpec S removed inserted).mpr hr⟩
    cases removed with
    | nil => exact False.elim (hn rfl)
    | cons x rest => rfl

theorem orderedCalibration : FiniteOccurrenceMatchingTargets.OrderedCalibration := by
  intro Symbol inst arity I P xs ys
  exact orderedSpec _ xs ys

theorem weakCalibration : FiniteOccurrenceMatchingTargets.WeakCalibration := by
  intro Symbol inst arity I P xs ys
  exact weakSpec _ xs ys

theorem replacementCalibration : FiniteOccurrenceMatchingTargets.ReplacementCalibration := by
  intro Symbol inst arity I P xs ys
  exact replacementSpec _ xs ys

theorem strictCalibration : FiniteOccurrenceMatchingTargets.StrictCalibration := by
  intro Symbol inst arity I P xs ys
  exact strictSpec _ _ xs ys

theorem liftOrdered {α β : Type} {W W' : α → β → Bool} (hW : ∀ s t,W s t ≤ W' s t)
    {xs : List α} {ys : List β} (h : List.Forall₂ (fun s t => W s t=true) xs ys) :
    List.Forall₂ (fun s t => W' s t=true) xs ys := by
  induction h with
  | nil => exact .nil
  | cons h rest ih => exact .cons (Bool.le_iff_imp.mp (hW _ _) h) ih

theorem positiveTests : FiniteOccurrenceMatchingTargets.PositiveTests := by
  intro α β W S W' S' hW hS xs ys
  constructor
  · apply Bool.le_iff_imp.mpr
    intro ht
    obtain ⟨zs,hz,hm⟩ := (weakSpec W xs ys).mp ht
    exact (weakSpec W' xs ys).mpr ⟨zs,hz,liftOrdered hW hm⟩
  · apply Bool.le_iff_imp.mpr
    intro ht
    obtain ⟨kept,removed,retained,inserted,hs,ht,hn,hw,hr⟩ := (strictSpec W S xs ys).mp ht
    apply (strictSpec W' S' xs ys).mpr
    refine ⟨kept,removed,retained,inserted,hs,ht,hn,liftOrdered hW hw,?_⟩
    intro t ht
    obtain ⟨s,hs,hst⟩ := hr t ht
    exact ⟨s,hs,Bool.le_iff_imp.mp (hS s t) hst⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatchingProof
