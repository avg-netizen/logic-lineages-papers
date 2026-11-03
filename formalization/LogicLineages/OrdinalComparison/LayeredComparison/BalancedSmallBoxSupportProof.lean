module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxClosureProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Proof
open BalancedSyntax

theorem outsideSupport {k : Nat} {Γ : List Nat} (C : Certificate (k :: Γ))
    (E : Upper k) (j : Fin k) (hn : E.outside j ≠ 0) {i : Nat}
    (hi : i ∈ rawVariables Γ C.1 (C.2 j)) : i ∈ rawVariables (k :: Γ) C E := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨j, by simp, ?_⟩
  simpa only [if_neg hn] using hi

theorem headSupport {k : Nat} {Γ : List Nat} (C : Certificate (k :: Γ))
    (E : Upper k) (a : Nat × Atom k) (ha : a ∈ E.atoms) (j : Fin k) {i : Nat}
    (hi : i ∈ rawVariables Γ C.1 (C.2 j)) : i ∈ rawVariables (k :: Γ) C E := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  exact List.mem_flatMap.mpr ⟨j, by simp, hi⟩

/-- Actual source support controls evaluation without any positivity or head
validity premise. The proof stays within the narrow syntax import closure. -/
theorem rawSupportStability : ∀ Γ : List Nat, ∀ C : Certificate Γ,
    ∀ E : Syntax Γ, ∀ ν μ : Nat → Nat,
    (∀ i ∈ rawVariables Γ C E, ν i = μ i) → value Γ C E ν = value Γ C E μ := by
  intro Γ
  induction Γ with
  | nil =>
    intro C E ν μ h
    exact BaseTermPrograms.Proof.supportStability E ν μ h
  | cons k Γ ih =>
    intro C E ν μ h
    cases hAtoms : E.atoms with
    | nil =>
      simp only [value, hAtoms, List.map_nil, List.sum_nil, Nat.add_zero]
      rw [Affine.Proof.affineZipOfFn, Affine.Proof.affineZipOfFn]
      apply congrArg (fun n => E.constant + n)
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext j
      by_cases hj : E.outside j = 0
      · simp only [hj, Nat.zero_mul]
      · rw [ih C.1 (C.2 j) ν μ (fun i hi => h i (outsideSupport C E j hj hi))]
    | cons a atoms =>
      have ha : a ∈ E.atoms := by rw [hAtoms]; exact List.mem_cons_self
      have hb : (fun j : Fin k => value Γ C.1 (C.2 j) ν) =
          (fun j : Fin k => value Γ C.1 (C.2 j) μ) := by
        funext j
        exact ih C.1 (C.2 j) ν μ (fun i hi => h i (headSupport C E a ha j hi))
      simp only [value]
      rw [hb]

/-- Every top-level raw name belongs to the same original common basis,
including names used only in the outside remainder. -/
theorem rawSupportWithinBasis {k : Nat} {Γ : List Nat} (C : Certificate (k :: Γ))
    (E : Upper k) {i : Nat} (hi : i ∈ rawVariables (k :: Γ) C E) :
    i ∈ basisSupport k Γ C := by
  rcases List.mem_append.mp hi with hout | hhead
  · obtain ⟨j, hj, hv⟩ := List.mem_flatMap.mp hout
    have hn : E.outside j ≠ 0 := by
      intro hz
      simp only [if_pos hz, List.not_mem_nil] at hv
    have hm : i ∈ rawVariables Γ C.1 (C.2 j) := by
      simpa only [if_neg hn] using hv
    exact List.mem_flatMap.mpr ⟨j, hj, hm⟩
  · obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hhead
    exact hv

theorem basisStabilityOfAtom {k : Nat} {Γ : List Nat} (C : Certificate (k :: Γ))
    (E : Upper k) (a : Nat × Atom k) (ha : a ∈ E.atoms) (ν μ : Nat → Nat)
    (h : ∀ i ∈ rawVariables (k :: Γ) C E, ν i = μ i) :
    basisValues k Γ C ν = basisValues k Γ C μ := by
  apply congrArg List.ofFn
  funext j
  exact rawSupportStability Γ C.1 (C.2 j) ν μ
    (fun i hi => h i (headSupport C E a ha j hi))

theorem actualSourceSupportStability : Targets.ActualSourceSupportStability := by
  intro k Γ C E F ν μ h
  have hE : ∀ i ∈ rawVariables (k :: Γ) C E, ν i = μ i :=
    fun i hi => h i (List.mem_append_left _ hi)
  have hF : ∀ i ∈ rawVariables (k :: Γ) C F, ν i = μ i :=
    fun i hi => h i (List.mem_append_right _ hi)
  have hb : (comparisonRow E F).atoms ≠ [] →
      basisValues k Γ C ν = basisValues k Γ C μ := by
    intro hn
    cases he : E.atoms with
    | cons a atoms =>
      exact basisStabilityOfAtom C E a (by rw [he]; exact List.mem_cons_self) ν μ hE
    | nil =>
      cases hf : F.atoms with
      | cons a atoms =>
        exact basisStabilityOfAtom C F a (by rw [hf]; exact List.mem_cons_self) ν μ hF
      | nil =>
        simp [comparisonRow, he, hf] at hn
  refine ⟨rawSupportStability _ C E ν μ hE, rawSupportStability _ C F ν μ hF, ?_, hb⟩
  by_cases hn : (comparisonRow E F).atoms = []
  · simp only [completeInputs, hn, List.map_nil]
  · simp only [completeInputs, hb hn]

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Proof
