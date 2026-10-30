module

public import LogicLineages.ComputabilityKnowledge.PredictionCommonFuelTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCommonFuelProof
open PredictionGame PredictionLearning PredictionUniformHistory PredictionCommonFuel
open PredictionCommonFuelTargets

theorem booleanHistoriesExact : BooleanHistoriesExact := by
  intro n
  induction n with
  | zero => intro xs; simp [booleanHistories]
  | succ n ih =>
    intro xs
    cases xs with
    | nil => simp [booleanHistories]
    | cons b xs => cases b <;> simp [booleanHistories, ih]

theorem booleanHistoriesPrimrec : BooleanHistoriesPrimrec := by
  have hf : Primrec (fun xs : List (List Bool) => xs.map (false :: ·)) :=
    Primrec.list_map Primrec.id ((Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂)
  have ht : Primrec (fun xs : List (List Bool) => xs.map (true :: ·)) :=
    Primrec.list_map Primrec.id ((Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂)
  apply (Primrec.nat_rec₁ [[]] ((Primrec.list_append.comp hf ht).comp Primrec.snd).to₂).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [booleanHistories] using (congrArg
      (fun xs : List (List Bool) => xs.map (false :: ·) ++ xs.map (true :: ·)) ih)

theorem commonFuelTestExact : CommonFuelTestExact := by
  intro v n s
  simp only [commonFuelTest, List.all_eq_true, List.mem_range]
  constructor
  · intro h k hk xs hx; exact h k (by omega) xs ((booleanHistoriesExact n xs).mpr hx)
  · intro h k hk xs hx; exact h k (by omega) xs ((booleanHistoriesExact n xs).mp hx)

private theorem pr_all {α β : Type} [Primcodable α] [Primcodable β]
    (l : α → List β) (p : α → β → Bool) (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec (fun a => (l a).all (p a)) := by
  have h := Primrec.list_foldr hl (Primrec.const true)
    (Primrec.to₂ (Primrec.and.comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)))
  apply h.of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons b bs ih => simp [List.all_cons, ih]

private abbrev TestData := Code × Nat × Nat

private theorem pr_one : Primrec (fun x : (TestData × Nat) × List Bool =>
    (boundedMove (compileSelfHistory x.1.1.1 x.1.2) x.1.1.2.2 x.2).isSome) := by
  have hv : Primrec (fun x : (TestData × Nat) × List Bool => x.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec (fun x : (TestData × Nat) × List Bool => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun x : (TestData × Nat) × List Bool => x.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.option_isSome.comp (PredictionLearningProof.pr_move.comp
    ((Nat.Partrec.Code.primrec₂_curry.comp hv hk).pair (hs.pair Primrec.snd)))

theorem commonFuelTestPrimrec : CommonFuelTestPrimrec := by
  have hinner : Primrec (fun x : TestData × Nat => (booleanHistories x.1.2.1).all
      (fun xs => (boundedMove (compileSelfHistory x.1.1 x.2) x.1.2.2 xs).isSome)) :=
    pr_all _ _ (booleanHistoriesPrimrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) pr_one.to₂
  exact pr_all _ _ (Primrec.list_range.comp
    (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))) hinner.to₂

private theorem finite_bound {α : Type} (l : List α) (P : α → Nat → Prop)
    (h : ∀ a ∈ l, ∃ F : Nat, ∀ s : Nat, F ≤ s → P a s) :
    ∃ F : Nat, ∀ s : Nat, F ≤ s → ∀ a ∈ l, P a s := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨A, hA⟩ := h a (by simp)
    obtain ⟨B, hB⟩ := ih (fun x hx => h x (by simp [hx]))
    refine ⟨max A B, ?_⟩
    intro s hs x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hA s ((Nat.le_max_left _ _).trans hs)
    · exact hB s ((Nat.le_max_right _ _).trans hs) x hx

theorem commonFuelEventuallySuccessful : CommonFuelEventuallySuccessful := by
  intro v ht n
  have h : ∀ k ∈ List.range (n + 1), ∃ F : Nat, ∀ s : Nat, F ≤ s →
      ∀ xs ∈ booleanHistories n, (boundedMove (compileSelfHistory v k) s xs).isSome = true := by
    intro k _
    apply finite_bound
    intro xs _
    obtain ⟨F, hF⟩ := PredictionLearningProof.move_complete (compileSelfHistory v k) (ht k) xs
    exact ⟨F, fun s hs => by rw [hF s hs]; rfl⟩
  obtain ⟨F, hF⟩ := finite_bound (List.range (n + 1)) _ h
  refine ⟨F, fun s hs => (commonFuelTestExact v n s).mpr ?_⟩
  intro k hk xs hx
  exact hF s hs k (List.mem_range.mpr (by omega)) xs ((booleanHistoriesExact n xs).mpr hx)

end LogicLineages.ComputabilityKnowledge.PredictionCommonFuelProof
