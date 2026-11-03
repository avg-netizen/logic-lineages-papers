module
public import LogicLineages.OrdinalComparison.SignedShiftCollectionAlgebraProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedShiftCollection.Proof

private theorem fold_max_spec (xs : List Nat) (seed : Nat) :
    seed ≤ xs.foldl max seed ∧
    (∀ x ∈ xs, x ≤ xs.foldl max seed) ∧
    (xs.foldl max seed = seed ∨ xs.foldl max seed ∈ xs) := by
  induction xs generalizing seed with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons]
    obtain ⟨hseed, hupper, hmem⟩ := ih (max seed a)
    refine ⟨(le_max_left seed a).trans hseed, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact (le_max_right seed a).trans hseed
      · exact hupper b hb
    · rcases hmem with he | hm
      · by_cases ha : a ≤ seed
        · left
          simpa only [max_eq_left ha] using he
        · right
          apply List.mem_cons.mpr
          left
          simpa only [max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge ha))] using he
      · exact Or.inr (List.mem_cons_of_mem a hm)

theorem actualGreatestSurvivingShift : Targets.ActualGreatestSurvivingShift := by
  intro row hne
  obtain ⟨hweighted, hnatural, hdistinct, hblocks, hsupport, hempty, hmass⟩ :=
    exactCollectionAndSupport row
  have hmax := fold_max_spec ((collected row).map Prod.snd) 0
  have hupper : ∀ a ∈ collected row, a.2 ≤ greatestKey row := by
    intro a ha
    exact hmax.2.1 a.2 (List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hkey : greatestKey row ∈ (collected row).map Prod.snd := by
    rcases hmax.2.2 with hzero | hmem
    · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil (collected row) hne
      have he : a.2 = greatestKey row := by
        have hu := hupper a ha
        change greatestKey row = 0 at hzero
        omega
      exact List.mem_map.mpr ⟨a, ha, he⟩
    · exact hmem
  obtain ⟨a, ha, hkeyeq⟩ := List.mem_map.mp hkey
  obtain ⟨hnonzero, hcoeff, b, hb, hbshift, hbkey⟩ := hblocks a ha
  have hlead : a.1 = leadingCoefficient row := by
    change a.1 = coefficient row (originalShift row (greatestKey row))
    simpa only [hkeyeq] using hcoeff
  have hpair : a = (leadingCoefficient row, greatestKey row) := by
    exact Prod.ext hlead hkeyeq
  refine ⟨hpair ▸ ha, ?_, hupper, ?_, ?_⟩
  · simpa only [hlead] using hnonzero
  · exact ⟨b, hb, by simpa only [greatestShift, hkeyeq] using hbshift⟩
  · intro c hc
    obtain ⟨d, hd, hdc⟩ := (hsupport c).mp hc
    have hu := hupper d hd
    change c ≤ originalShift row (greatestKey row)
    rw [← hdc]
    unfold originalShift
    omega

end LogicLineages.OrdinalComparison.SignedShiftCollection.Proof
