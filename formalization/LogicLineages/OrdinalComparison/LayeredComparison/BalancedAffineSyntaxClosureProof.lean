module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Affine.Proof

/-- Ordered pointwise arithmetic of the actual finite basis. -/
theorem affineZipOfFn {A B D : Type} {k : Nat} (f : Fin k → A) (g : Fin k → B)
    (h : A → B → D) :
    (List.ofFn f).zipWith h (List.ofFn g) = List.ofFn (fun j => h (f j) (g j)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem sumOfFnAdd (k : Nat) : ∀ f g : Fin k → Nat,
    (List.ofFn (fun j => f j + g j)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction k with
  | zero => intro f g; rfl
  | succ k ih =>
    intro f g
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    simp only [List.sum_cons, ih]
    omega

theorem value_numeral (Γ : List Nat) (C : Certificate Γ) (n : Nat) (ν : Nat → Nat) :
    value Γ C (numeral Γ n) ν = n := by
  cases Γ with
  | nil => rfl
  | cons k Γ =>
    simp only [numeral, value, affineZipOfFn]
    simp

theorem genuine_numeral (Γ : List Nat) (n : Nat) :
    genuineExpression Γ (numeral Γ n) := by
  cases Γ <;> simp [numeral, genuineExpression]

theorem rawVariables_numeral (Γ : List Nat) (C : Certificate Γ) (n : Nat) :
    rawVariables Γ C (numeral Γ n) = [] := by
  cases Γ <;> simp [numeral, rawVariables, CommonLayerSyntax.BaseTerm.variables]

theorem value_add (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ) (ν : Nat → Nat) :
    value Γ C (add Γ E F) ν = value Γ C E ν + value Γ C F ν := by
  cases Γ with
  | nil => rfl
  | cons k Γ =>
    simp only [add, value, affineZipOfFn, Nat.add_mul,
      List.map_append, List.sum_append, sumOfFnAdd]
    omega

theorem genuine_add (Γ : List Nat) (E F : Syntax Γ)
    (hE : genuineExpression Γ E) (hF : genuineExpression Γ F) :
    genuineExpression Γ (add Γ E F) := by
  cases Γ with
  | nil => trivial
  | cons k Γ =>
    intro a ha
    rcases List.mem_append.mp ha with he | hf
    · exact hE a he
    · exact hF a hf

private theorem mem_zero_test (n : Nat) (xs : List Nat) (i : Nat) :
    i ∈ (if n = 0 then [] else xs) ↔ n ≠ 0 ∧ i ∈ xs := by
  by_cases h : n = 0 <;> simp [h]

private theorem mem_upper (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E : Upper k) (i : Nat) :
    i ∈ rawVariables (k :: Γ) C E ↔
      (∃ j : Fin k, E.outside j ≠ 0 ∧ i ∈ rawVariables Γ C.1 (C.2 j)) ∨
      (∃ a ∈ E.atoms, ∃ j : Fin k, i ∈ rawVariables Γ C.1 (C.2 j)) := by
  simp only [rawVariables, List.mem_append, List.mem_flatMap,
    List.mem_finRange, true_and, mem_zero_test]

theorem mem_rawVariables_add (Γ : List Nat) (C : Certificate Γ)
    (E F : Syntax Γ) (i : Nat) :
    i ∈ rawVariables Γ C (add Γ E F) ↔
      i ∈ rawVariables Γ C E ∨ i ∈ rawVariables Γ C F := by
  cases Γ with
  | nil =>
    exact List.mem_append
  | cons k Γ =>
    simp only [mem_upper, add, List.mem_append]
    constructor
    · rintro (⟨j, hn, hi⟩ | ⟨a, ha, j, hi⟩)
      · have hc : E.outside j ≠ 0 ∨ F.outside j ≠ 0 := by omega
        rcases hc with he | hf
        · exact Or.inl (Or.inl ⟨j, he, hi⟩)
        · exact Or.inr (Or.inl ⟨j, hf, hi⟩)
      · rcases ha with he | hf
        · exact Or.inl (Or.inr ⟨a, he, j, hi⟩)
        · exact Or.inr (Or.inr ⟨a, hf, j, hi⟩)
    · rintro ((⟨j, hn, hi⟩ | ⟨a, ha, j, hi⟩) |
        (⟨j, hn, hi⟩ | ⟨a, ha, j, hi⟩))
      · exact Or.inl ⟨j, by omega, hi⟩
      · exact Or.inr ⟨a, Or.inl ha, j, hi⟩
      · exact Or.inl ⟨j, by omega, hi⟩
      · exact Or.inr ⟨a, Or.inr ha, j, hi⟩

theorem scale_zero (Γ : List Nat) (E : Syntax Γ) :
    scale Γ 0 E = numeral Γ 0 := rfl

theorem scale_succ (Γ : List Nat) (n : Nat) (E : Syntax Γ) :
    scale Γ (n + 1) E = add Γ E (scale Γ n E) := by
  simp only [scale, List.replicate_succ, List.foldr_cons]

theorem value_scale (Γ : List Nat) (C : Certificate Γ) (n : Nat)
    (E : Syntax Γ) (ν : Nat → Nat) :
    value Γ C (scale Γ n E) ν = n * value Γ C E ν := by
  induction n with
  | zero => simp only [scale_zero, value_numeral, Nat.zero_mul]
  | succ n ih =>
    rw [scale_succ, value_add, ih, Nat.succ_mul]
    omega

theorem genuine_scale (Γ : List Nat) (n : Nat) (E : Syntax Γ)
    (hE : genuineExpression Γ E) : genuineExpression Γ (scale Γ n E) := by
  induction n with
  | zero => exact genuine_numeral Γ 0
  | succ n ih =>
    rw [scale_succ]
    exact genuine_add Γ E (scale Γ n E) hE ih

theorem mem_rawVariables_scale (Γ : List Nat) (C : Certificate Γ)
    (n : Nat) (E : Syntax Γ) (i : Nat) :
    i ∈ rawVariables Γ C (scale Γ n E) ↔ n ≠ 0 ∧ i ∈ rawVariables Γ C E := by
  induction n with
  | zero => simp only [scale_zero, rawVariables_numeral, List.not_mem_nil,
      ne_eq, not_true_eq_false, false_and]
  | succ n ih =>
    rw [scale_succ, mem_rawVariables_add, ih]
    constructor
    · intro h
      exact ⟨by omega, h.elim id And.right⟩
    · rintro ⟨_, hi⟩
      exact Or.inl hi

theorem value_fold (Γ : List Nat) (C : Certificate Γ) (Es : List (Syntax Γ))
    (ν : Nat → Nat) :
    value Γ C (Es.foldr (add Γ) (numeral Γ 0)) ν =
      (Es.map (fun E => value Γ C E ν)).sum := by
  induction Es with
  | nil => simp only [List.foldr_nil, value_numeral, List.map_nil, List.sum_nil]
  | cons E Es ih =>
    simp only [List.foldr_cons, value_add, List.map_cons, List.sum_cons, ih]

theorem genuine_fold (Γ : List Nat) (Es : List (Syntax Γ)) :
    (∀ E ∈ Es, genuineExpression Γ E) →
      genuineExpression Γ (Es.foldr (add Γ) (numeral Γ 0)) := by
  induction Es with
  | nil => intro _; exact genuine_numeral Γ 0
  | cons E Es ih =>
    intro h
    apply genuine_add
    · exact h E (by simp)
    · exact ih (fun F hF => h F (List.mem_cons_of_mem E hF))

theorem mem_rawVariables_fold (Γ : List Nat) (C : Certificate Γ)
    (Es : List (Syntax Γ)) (i : Nat) :
    i ∈ rawVariables Γ C (Es.foldr (add Γ) (numeral Γ 0)) ↔
      ∃ E ∈ Es, i ∈ rawVariables Γ C E := by
  induction Es with
  | nil => simp only [List.foldr_nil, rawVariables_numeral, List.not_mem_nil,
      false_and, exists_false]
  | cons E Es ih =>
    simp only [List.foldr_cons, mem_rawVariables_add, ih, List.mem_cons,
      or_and_right, exists_or, exists_eq_left]

/-- Literal affine evaluation uses the original shared certificate and basis. -/
theorem value_combination (Γ : List Nat) (C : Certificate Γ) (k c : Nat)
    (coefficients : Fin k → Nat) (basis : Fin k → Syntax Γ) (ν : Nat → Nat) :
    value Γ C (combination Γ k c coefficients basis) ν =
      c + ((List.ofFn coefficients).zipWith (· * ·)
        (List.ofFn (fun j => value Γ C (basis j) ν))).sum := by
  simp only [combination, value_add, value_numeral, value_fold, List.map_ofFn,
    Function.comp_def, value_scale, affineZipOfFn]

/-- Zero coefficients remove support; repeated or dependent basis entries remain valid. -/
theorem mem_rawVariables_combination (Γ : List Nat) (C : Certificate Γ) (k c : Nat)
    (coefficients : Fin k → Nat) (basis : Fin k → Syntax Γ) (i : Nat) :
    i ∈ rawVariables Γ C (combination Γ k c coefficients basis) ↔
      ∃ j : Fin k, coefficients j ≠ 0 ∧ i ∈ rawVariables Γ C (basis j) := by
  rw [combination, mem_rawVariables_add, rawVariables_numeral]
  simp only [List.not_mem_nil, false_or, mem_rawVariables_fold]
  constructor
  · rintro ⟨E, hE, hi⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    exact ⟨j, (mem_rawVariables_scale Γ C (coefficients j) (basis j) i).mp hi⟩
  · rintro ⟨j, hn, hi⟩
    exact ⟨scale Γ (coefficients j) (basis j), List.mem_ofFn.mpr ⟨j, rfl⟩,
      (mem_rawVariables_scale Γ C (coefficients j) (basis j) i).mpr ⟨hn, hi⟩⟩

theorem genuine_combination (Γ : List Nat) (k c : Nat)
    (coefficients : Fin k → Nat) (basis : Fin k → Syntax Γ)
    (h : ∀ j, genuineExpression Γ (basis j)) :
    genuineExpression Γ (combination Γ k c coefficients basis) := by
  unfold combination
  apply genuine_add
  · exact genuine_numeral Γ c
  · apply genuine_fold
    intro E hE
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    exact genuine_scale Γ (coefficients j) (basis j) (h j)

theorem literalAffineClosure : Targets.LiteralAffineClosure := by
  intro Γ C ν
  exact ⟨fun n => ⟨value_numeral Γ C n ν, genuine_numeral Γ n⟩,
    fun E F => ⟨value_add Γ C E F ν, genuine_add Γ E F⟩,
    fun n E => ⟨value_scale Γ C n E ν, genuine_scale Γ n E⟩⟩

theorem exactAffineSupport : Targets.ExactAffineSupport := by
  intro Γ C
  exact ⟨rawVariables_numeral Γ C, mem_rawVariables_add Γ C, mem_rawVariables_scale Γ C⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Affine.Proof
