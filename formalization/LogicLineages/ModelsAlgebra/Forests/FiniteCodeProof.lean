module

public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeTargets
public import LogicLineages.ModelsAlgebra.Forests.HostReductionProof
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.FiniteCodeProof

open FiniteCode

attribute [local instance] Classical.propDecidable

theorem valid_iff (c : Code) : valid c = true ↔ ForestPredicate c := by simp [valid]

theorem forestCodeCodecFaithful : Targets.ForestCodeCodecFaithful := by
  intro c
  exact Encodable.encodek c

theorem forestCodeValidation : Targets.ForestCodeValidation := by
  intro c
  rw [valid_iff]
  constructor
  · intro hc
    have hvalid : valid c = true := (valid_iff c).mpr hc
    exact ⟨hc.1, (toForest c hvalid).carrierPartialOrder, (toForest c hvalid).forest,
      fun _ _ => Iff.rfl⟩
  · rintro ⟨hend, po, hforest, hrel⟩
    letI : PartialOrder (Fin c.1) := po
    refine ⟨hend, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact (hrel ⟨i, List.mem_range.mp hi⟩ ⟨i, List.mem_range.mp hi⟩).mp le_rfl
    · intro i hi j hj hij hji
      have he := le_antisymm ((hrel ⟨i, List.mem_range.mp hi⟩ ⟨j, List.mem_range.mp hj⟩).mpr hij)
        ((hrel ⟨j, List.mem_range.mp hj⟩ ⟨i, List.mem_range.mp hi⟩).mpr hji)
      exact congrArg Fin.val he
    · intro i hi j hj k hk hij hjk
      exact (hrel ⟨i, List.mem_range.mp hi⟩ ⟨k, List.mem_range.mp hk⟩).mp
        (le_trans ((hrel ⟨i, List.mem_range.mp hi⟩ ⟨j, List.mem_range.mp hj⟩).mpr hij)
          ((hrel ⟨j, List.mem_range.mp hj⟩ ⟨k, List.mem_range.mp hk⟩).mpr hjk))
    · intro i hi j hj k hk hik hjk
      rcases hforest ((hrel ⟨i, List.mem_range.mp hi⟩ ⟨k, List.mem_range.mp hk⟩).mpr hik)
          ((hrel ⟨j, List.mem_range.mp hj⟩ ⟨k, List.mem_range.mp hk⟩).mpr hjk) with hij | hji
      · exact Or.inl ((hrel _ _).mp hij)
      · exact Or.inr ((hrel _ _).mp hji)

theorem allPairs_mem (n i j : ℕ) : (i, j) ∈ allPairs n ↔ i < n ∧ j < n := by
  simp [allPairs]

theorem allRelations_mem (n : ℕ) (c : Code) :
    c ∈ allRelations n ↔ c.1 = n ∧ c.2.Sublist (allPairs n) := by
  rcases c with ⟨m, edges⟩
  simp [allRelations, List.mem_sublists, eq_comm, and_comm]

theorem hostCodes_mem (N : ℕ) (c : Code) :
    c ∈ hostCodes N ↔ c.1 ≤ N ∧ c.2.Sublist (allPairs c.1) := by
  simp only [hostCodes, List.mem_flatMap]
  constructor
  · rintro ⟨n, hn, hc⟩
    obtain ⟨hm, he⟩ := (allRelations_mem n c).mp hc
    subst n
    exact ⟨by have := List.mem_range.mp hn; omega, he⟩
  · rintro ⟨hn, he⟩
    exact ⟨c.1, List.mem_range.mpr (by omega), (allRelations_mem _ _).mpr ⟨rfl, he⟩⟩

noncomputable def canonicalCode (F : FiniteOrderForest) : Code :=
  (Fintype.card F.Carrier, (allPairs (Fintype.card F.Carrier)).filter fun ij =>
    decide (∃ i j : Fin (Fintype.card F.Carrier), i.val = ij.1 ∧ j.val = ij.2 ∧
      (Fintype.equivFin F.Carrier).symm i ≤ (Fintype.equivFin F.Carrier).symm j))

theorem canonical_rel (F : FiniteOrderForest) (i j : Fin (Fintype.card F.Carrier)) :
    Rel (canonicalCode F) i.val j.val ↔
      (Fintype.equivFin F.Carrier).symm i ≤ (Fintype.equivFin F.Carrier).symm j := by
  simp only [Rel, canonicalCode, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, i', j', hi, hj, hij⟩
    have ei : i' = i := Fin.ext hi
    have ej : j' = j := Fin.ext hj
    simpa [ei, ej] using hij
  · intro h
    exact ⟨(allPairs_mem _ _ _).mpr ⟨i.isLt, j.isLt⟩, i, j, rfl, rfl, h⟩

theorem canonical_valid (F : FiniteOrderForest) : valid (canonicalCode F) = true := by
  apply (valid_iff _).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hm := (List.mem_filter.mp he).1
    exact (allPairs_mem _ _ _).mp hm
  · intro i hi
    exact (canonical_rel F ⟨i, List.mem_range.mp hi⟩ ⟨i, List.mem_range.mp hi⟩).mpr le_rfl
  · intro i hi j hj hij hji
    have h₁ := (canonical_rel F ⟨i, List.mem_range.mp hi⟩ ⟨j, List.mem_range.mp hj⟩).mp hij
    have h₂ := (canonical_rel F ⟨j, List.mem_range.mp hj⟩ ⟨i, List.mem_range.mp hi⟩).mp hji
    exact congrArg Fin.val ((Fintype.equivFin F.Carrier).symm.injective (le_antisymm h₁ h₂))
  · intro i hi j hj k hk hij hjk
    exact (canonical_rel F ⟨i, List.mem_range.mp hi⟩ ⟨k, List.mem_range.mp hk⟩).mpr
      (le_trans ((canonical_rel F ⟨i, List.mem_range.mp hi⟩ ⟨j, List.mem_range.mp hj⟩).mp hij)
        ((canonical_rel F ⟨j, List.mem_range.mp hj⟩ ⟨k, List.mem_range.mp hk⟩).mp hjk))
  · intro i hi j hj k hk hik hjk
    rcases F.forest ((canonical_rel F ⟨i, List.mem_range.mp hi⟩ ⟨k, List.mem_range.mp hk⟩).mp hik)
        ((canonical_rel F ⟨j, List.mem_range.mp hj⟩ ⟨k, List.mem_range.mp hk⟩).mp hjk) with hij | hji
    · exact Or.inl ((canonical_rel F _ _).mpr hij)
    · exact Or.inr ((canonical_rel F _ _).mpr hji)

noncomputable def canonicalIso (F : FiniteOrderForest) :
    F.Carrier ≃o (toForest (canonicalCode F) (canonical_valid F)).Carrier where
  toEquiv := Fintype.equivFin F.Carrier
  map_rel_iff' := by
    intro x y
    change Rel (canonicalCode F) ((Fintype.equivFin F.Carrier) x).val
      ((Fintype.equivFin F.Carrier) y).val ↔ x ≤ y
    rw [canonical_rel]
    simp

theorem forestCodeEnumeration : Targets.ForestCodeEnumeration := by
  refine ⟨allRelations_mem, hostCodes_mem, ?_⟩
  intro F
  refine ⟨canonicalCode F, (allRelations_mem _ _).mpr ⟨rfl, ?_⟩,
    canonical_valid F, ⟨canonicalIso F⟩⟩
  exact List.filter_sublist

theorem forestMapWordEnumeration : Targets.ForestMapWordEnumeration := by
  intro n m xs
  induction n generalizing xs with
  | zero => cases xs <;> simp [mapWords]
  | succ n ih =>
      cases xs with
      | nil => simp [mapWords]
      | cons a xs =>
          simp [mapWords, ih, and_assoc, and_left_comm, and_comm]

theorem getD_bound (xs : List ℕ) (n m : ℕ) (hlen : xs.length = n)
    (hb : ∀ a ∈ xs, a < m) (i : Fin n) : xs.getD i.val 0 < m := by
  rw [List.getD_eq_getElem xs 0 (by simpa [hlen] using i.isLt)]
  exact hb _ (List.getElem_mem _)

theorem forestMapTestCorrect : Targets.ForestMapTestCorrect := by
  intro c d hc hd xs
  change decide (MapPredicate c d xs) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hlen, hb, hi, hr⟩
    let e : (toForest c hc).Carrier ↪o (toForest d hd).Carrier := {
      toFun := fun i => ⟨xs.getD i.val 0, getD_bound xs c.1 d.1 hlen hb i⟩
      inj' := fun i j hij => Fin.ext (hi i.val (List.mem_range.mpr i.isLt)
        j.val (List.mem_range.mpr j.isLt) (congrArg Fin.val hij))
      map_rel_iff' := fun {i j} => hr i.val (List.mem_range.mpr i.isLt)
        j.val (List.mem_range.mpr j.isLt) }
    exact ⟨hlen, hb, e, fun _ => rfl⟩
  · rintro ⟨hlen, hb, e, he⟩
    refine ⟨hlen, hb, ?_, ?_⟩
    · intro i hi j hj hij
      have hEq : e ⟨i, List.mem_range.mp hi⟩ = e ⟨j, List.mem_range.mp hj⟩ := by
        apply Fin.ext
        simpa only [he] using hij
      exact congrArg Fin.val (e.injective hEq)
    · intro i hi j hj
      have hr := e.le_iff_le (a := ⟨i, List.mem_range.mp hi⟩) (b := ⟨j, List.mem_range.mp hj⟩)
      change Rel d (e ⟨i, List.mem_range.mp hi⟩).val (e ⟨j, List.mem_range.mp hj⟩).val ↔ Rel c i j at hr
      simpa only [he] using hr

theorem ofFn_getD (c d : Code) (hc : valid c = true) (hd : valid d = true)
    (e : (toForest c hc).Carrier ↪o (toForest d hd).Carrier) (i : Fin c.1) :
    (List.ofFn fun j : Fin c.1 => (e j).val).getD i.val 0 = (e i).val := by
  rw [List.getD_eq_getElem _ 0 (by simpa using i.isLt)]
  simp

theorem forestEmbeddingTestCorrect : Targets.ForestEmbeddingTestCorrect := by
  intro c d hc hd
  change decide (EmbeddingPredicate c d) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨xs, hm, hx⟩
    obtain ⟨_, _, e, _⟩ := (forestMapTestCorrect c d hc hd xs).mp (by simpa [mapTest] using hx)
    exact ⟨e⟩
  · rintro ⟨e⟩
    let xs := List.ofFn fun i : Fin c.1 => (e i).val
    have hlen : xs.length = c.1 := by simp [xs]
    have hb : ∀ a ∈ xs, a < d.1 := by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact (e i).isLt
    refine ⟨xs, (forestMapWordEnumeration _ _ _).mpr ⟨hlen, hb⟩, ?_⟩
    have hh := (forestMapTestCorrect c d hc hd xs).mpr
      ⟨hlen, hb, e, fun i => (ofFn_getD c d hc hd e i).symm⟩
    simpa [mapTest] using hh

theorem forestAvoidanceTestCorrect : Targets.ForestAvoidanceTestCorrect := by
  intro U hU c hc
  change decide (PermittedPredicate U c) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨_, hp⟩ B hB hEmb
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    apply (hp b.val b.property).2
    have he := (forestEmbeddingTestCorrect b.val c (hU b.val b.property) hc).mpr hEmb
    simpa [embeddingTest] using he
  · intro hAvoid
    refine ⟨(valid_iff c).mp hc, ?_⟩
    intro B hB
    refine ⟨(valid_iff B).mp (hU B hB), ?_⟩
    intro hEmb
    apply hAvoid (toForest B (hU B hB))
      (List.mem_map.mpr ⟨⟨B, hB⟩, by simp, rfl⟩)
    exact (forestEmbeddingTestCorrect B c (hU B hB) hc).mp (by simpa [embeddingTest] using hEmb)

theorem forestBoundedHostTestCorrect : Targets.ForestBoundedHostTestCorrect := by
  intro U hU c d hc hd
  change decide (BoundedHostPredicate U c d) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨H, hm, hp, hf, hg⟩
    have hH : valid H = true := (valid_iff H).mpr hp.1
    exact ⟨toForest H hH,
      (forestAvoidanceTestCorrect U hU H hH).mp (by simpa [permittedTest] using hp),
      (forestEmbeddingTestCorrect c H hc hH).mp (by simpa [embeddingTest] using hf),
      (forestEmbeddingTestCorrect d H hd hH).mp (by simpa [embeddingTest] using hg)⟩
  · intro hHost
    obtain ⟨K, hK, ⟨f⟩, ⟨g⟩, hcard⟩ :=
      (HostReductionProof.boundedCommonHost (toFamily U hU) (toForest c hc) (toForest d hd)).mp hHost
    let H := canonicalCode K
    have hH : valid H = true := canonical_valid K
    let e := canonicalIso K
    have hsub : H.2.Sublist (allPairs H.1) := List.filter_sublist
    have hsize : H.1 ≤ c.1 + d.1 := by
      change Fintype.card K.Carrier ≤ c.1 + d.1
      have cc : Fintype.card (toForest c hc).Carrier = c.1 :=
        (@Fintype.card_congr (toForest c hc).Carrier (Fin c.1)
          (toForest c hc).carrierFintype inferInstance (Equiv.refl _)).trans (Fintype.card_fin _)
      have cd : Fintype.card (toForest d hd).Carrier = d.1 :=
        (@Fintype.card_congr (toForest d hd).Carrier (Fin d.1)
          (toForest d hd).carrierFintype inferInstance (Equiv.refl _)).trans (Fintype.card_fin _)
      simpa only [cc, cd] using hcard
    have hAvoid : AvoidsForbidden (toFamily U hU) (toForest H hH).Carrier :=
      HostReductionProof.forbiddenAvoidanceHereditary _ _ _ e.symm.toOrderEmbedding hK
    refine ⟨H, (hostCodes_mem _ _).mpr ⟨hsize, hsub⟩, ?_, ?_, ?_⟩
    · have hp := (forestAvoidanceTestCorrect U hU H hH).mpr hAvoid
      simpa [permittedTest] using hp
    · have hp := (forestEmbeddingTestCorrect c H hc hH).mpr ⟨f.trans e.toOrderEmbedding⟩
      simpa [embeddingTest] using hp
    · have hp := (forestEmbeddingTestCorrect d H hd hH).mpr ⟨g.trans e.toOrderEmbedding⟩
      simpa [embeddingTest] using hp

theorem forestNegativePairTestCorrect : Targets.ForestNegativePairTestCorrect := by
  intro U hU c d hc hd
  simp only [negativePairTest, Bool.and_eq_true, Bool.not_eq_true']
  rw [forestAvoidanceTestCorrect U hU c hc, forestAvoidanceTestCorrect U hU d hd]
  have he := forestBoundedHostTestCorrect U hU c d hc hd
  have hn : boundedHostTest U c d = false ↔ ¬ ∃ H : FiniteOrderForest,
      AvoidsForbidden (toFamily U hU) H.Carrier ∧
        Nonempty ((toForest c hc).Carrier ↪o H.Carrier) ∧
        Nonempty ((toForest d hd).Carrier ↪o H.Carrier) := by
    rw [← he]
    cases boundedHostTest U c d <;> simp
  rw [hn]
  tauto

end LogicLineages.ModelsAlgebra.Forests.FiniteCodeProof
