module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundsTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalBounds

private theorem inputMax_le (g : Nat → Nat → Nat) (i n b : Nat) :
    inputMax g i n ≤ b ↔ ∀ j, j ≤ n → g i j ≤ b := by
  induction n with
  | zero => simp [inputMax]
  | succ n ih =>
    rw [inputMax, max_le_iff, ih]
    constructor
    · rintro ⟨h, hn⟩ j hj
      by_cases hle : j ≤ n
      · exact h j hle
      · have heq : j=n+1 := by omega
        simpa only [heq] using hn
    · intro h
      exact ⟨fun j hj => h j (by omega), h (n+1) le_rfl⟩

private theorem levelBound_le (g : Nat → Nat → Nat) (m n b : Nat) :
    levelBound g m n ≤ b ↔ ∀ i, i < m → ∀ j, j ≤ n → g i j ≤ b := by
  induction m with
  | zero => simp [levelBound]
  | succ m ih =>
    rw [levelBound, max_le_iff, ih, inputMax_le]
    constructor
    · rintro ⟨h, hm⟩ i hi j hj
      by_cases hlt : i<m
      · exact h i hlt j hj
      · have heq : i=m := by omega
        subst i
        exact hm j hj
    · intro h
      exact ⟨fun i hi j hj => h i (by omega) j hj, h m (by omega)⟩

private theorem entry_le (g : Nat → Nat → Nat) (m n i j : Nat) (hi : i<m) (hj : j≤n) :
    g i j ≤ levelBound g m n :=
  (levelBound_le g m n (levelBound g m n)).mp le_rfl i hi j hj

theorem literalFiniteMaximum : Targets.LiteralFiniteMaximum := by
  intro g m n
  apply le_antisymm
  · apply (levelBound_le g m n _).mpr
    intro i hi j hj
    exact Finset.le_sup_of_le (Finset.mem_range.mpr hi)
      (Finset.le_sup_of_le (Finset.mem_range.mpr (by omega)) le_rfl)
  · apply Finset.sup_le
    intro i hi
    apply Finset.sup_le
    intro j hj
    exact entry_le g m n i j (Finset.mem_range.mp hi) (by have := Finset.mem_range.mp hj; omega)

private theorem inputMax_computable (g : Nat → Nat → Nat) (hg : Computable₂ g) :
    Computable₂ (inputMax g) := by
  have hs : Computable (fun p : (Nat × Nat) × (Nat × Nat) =>
      max p.2.2 (g p.1.1 (p.2.1+1))) :=
    Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hg.comp (Computable.fst.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))
  have h := Computable.nat_rec (Computable.snd : Computable (fun p : Nat × Nat => p.2))
    (hg.comp Computable.fst (Computable.const 0)) hs.to₂
  change Computable (fun p : Nat × Nat => inputMax g p.1 p.2)
  apply h.of_eq
  rintro ⟨i,n⟩
  induction n with
  | zero => rfl
  | succ n ih => simp [inputMax, ih]

theorem computableBounds : Targets.ComputableBounds := by
  intro g hg
  have hp := inputMax_computable g hg
  have hs : Computable (fun p : (Nat × Nat) × (Nat × Nat) =>
      max p.2.2 (inputMax g p.2.1 p.1.2)) :=
    Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hp.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.fst))
  have h := Computable.nat_rec (Computable.fst : Computable (fun p : Nat × Nat => p.1))
    (Computable.const 0) hs.to₂
  have hl : Computable₂ (levelBound g) := by
    change Computable (fun p : Nat × Nat => levelBound g p.1 p.2)
    apply h.of_eq
    rintro ⟨m,n⟩
    induction m with
    | zero => rfl
    | succ m ih => simp [levelBound, ih]
  exact ⟨hl, hl.comp Computable.succ Computable.id⟩

private theorem inputMax_primrec (g : Nat → Nat → Nat) (i : Nat) (hg : Primrec (g i)) :
    Primrec (inputMax g i) := by
  have hs : Primrec₂ (fun n v : Nat => max v (g i (n+1))) :=
    (Primrec.nat_max.comp Primrec.snd (hg.comp (Primrec.succ.comp Primrec.fst))).to₂
  apply (Primrec.nat_rec₁ (g i 0) hs).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [inputMax, ih]

theorem fixedLevelPrimitiveRecursive : Targets.FixedLevelPrimitiveRecursive := by
  intro g hg m
  induction m with
  | zero => exact Primrec.const 0
  | succ m ih => exact Primrec.nat_max.comp ih (inputMax_primrec g m (hg m))

theorem monotoneLevels : Targets.MonotoneLevels := by
  intro g n a b hab
  apply (levelBound_le g a n _).mpr
  intro i hi j hj
  exact entry_le g b n i j (by omega) hj

theorem monotoneInputs : Targets.MonotoneInputs := by
  intro g m a b hab
  apply (levelBound_le g m a _).mpr
  intro i hi j hj
  exact entry_le g m b i j hi (by omega)

theorem diagonalDominance : Targets.DiagonalDominance := by
  intro g m
  refine ⟨m, ?_⟩
  intro n hn
  exact monotoneLevels g n (by omega : m ≤ n+1)

theorem successorTail : Targets.SuccessorTail := by
  intro g hg
  obtain ⟨i, hi⟩ := hg Nat.succ Primrec.succ
  refine ⟨i+1, by omega, ?_⟩
  intro m hm n
  have h := entry_le g m n i n (by omega) le_rfl
  simpa only [hi] using h

theorem evaderLevelTail : Targets.EvaderLevelTail := by
  intro g hg
  obtain ⟨m₀, hm₀, hb⟩ := successorTail g hg
  refine ⟨m₀, hm₀, ?_⟩
  intro m hm k
  refine ⟨k+2, ?_⟩
  intro n hn
  have hbound := hb m hm n
  have hmin := Nat.min_le_left k n
  omega

theorem evaderDiagonalTail : Targets.EvaderDiagonalTail := by
  intro g hg k
  obtain ⟨m₀, hm₀, hb⟩ := successorTail g hg
  refine ⟨max m₀ (k+2), ?_⟩
  intro n hn
  have hbound := hb (n+1) (by omega) n
  have hmin := Nat.min_le_left k n
  change min k n+2 < levelBound g (n+1) n
  omega
end LogicLineages.ComputabilityKnowledge.PredictionOriginalBounds
