module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsMaskProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards.Proof
open BalancedSyntax
open BalancedSyntax.Affine
open BalancedSyntax.Affine.Proof

theorem sourceTerms_length (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) :
    (sourceTerms k Γ C E F).length = (sourceCoefficients E F).length + 2 := by
  simp [sourceTerms, sourceCoefficients]

theorem sourceTerms_values (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (ν : Nat → Nat) :
    (sourceTerms k Γ C E F).map (fun T => value Γ C.1 T ν) =
      ((comparisonRow E F).atoms.map (fun a =>
        BalancedRow.input (basisValues k Γ C ν) a.2)) ++
        [value Γ C.1 (lowerPart k Γ C E) ν,
         value Γ C.1 (lowerPart k Γ C F) ν] := by
  simp only [sourceTerms, signedAtoms, comparisonRow, List.map_append,
    List.map_map, Function.comp_def, List.map_cons, List.map_nil, value_completeInput]

theorem sourceTerm_lowerLeft (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) :
    sourceTerm k Γ C E F (sourceCoefficients E F).length = lowerPart k Γ C E := by
  unfold sourceTerm sourceTerms
  simp only [sourceCoefficients, List.length_map]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem sourceTerm_lowerRight (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) :
    sourceTerm k Γ C E F ((sourceCoefficients E F).length + 1) = lowerPart k Γ C F := by
  unfold sourceTerm sourceTerms
  simp only [sourceCoefficients, List.length_map]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem sourceValuation_input (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (ν : Nat → Nat)
    (i : Nat) (hi : i < (comparisonRow E F).atoms.length) :
    sourceValuation k Γ C E F ν i =
      BalancedRow.input (basisValues k Γ C ν) ((comparisonRow E F).atoms[i]).2 := by
  calc
    sourceValuation k Γ C E F ν i =
        ((sourceTerms k Γ C E F).map (fun T => value Γ C.1 T ν)).getD i 0 := by
      have hm := List.getD_map (sourceTerms k Γ C E F) (numeral Γ 0)
        (n := i) (fun T => value Γ C.1 T ν)
      rw [value_numeral] at hm
      exact hm.symm
    _ = ((comparisonRow E F).atoms.map (fun a =>
        BalancedRow.input (basisValues k Γ C ν) a.2)).getD i 0 := by
      rw [sourceTerms_values, List.getD_append _ _ _ _ (by simpa using hi)]
    _ = BalancedRow.input (basisValues k Γ C ν) ((comparisonRow E F).atoms[i]).2 := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_map]

theorem sourceTerms_genuine (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k)
    (hC : genuineCertificate (k :: Γ) C) :
    ∀ T ∈ sourceTerms k Γ C E F, genuineExpression Γ T := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hT
    exact genuine_combination Γ k (actualOrdinalNorm a.2.head.1.repr + a.2.offset)
      (fun j => a.2.factors j + 1) C.2 hC.2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact genuine_combination Γ k E.constant E.outside C.2 hC.2
    · exact genuine_combination Γ k F.constant F.outside C.2 hC.2

theorem literalSourceLabels : Targets.LiteralSourceLabels := by
  intro k Γ C E F ν
  refine ⟨sourceTerms_length k Γ C E F, sourceTerms_values k Γ C E F ν, ?_, ?_, ?_⟩
  · change value Γ C.1 (sourceTerm k Γ C E F (sourceCoefficients E F).length) ν = _
    rw [sourceTerm_lowerLeft]
  · change value Γ C.1
      (sourceTerm k Γ C E F ((sourceCoefficients E F).length + 1)) ν = _
    rw [sourceTerm_lowerRight]
  · exact sourceTerms_genuine k Γ C E F

private theorem outside_support (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E : Upper k)
    (j : Fin k) (hn : E.outside j ≠ 0) (i : Nat)
    (hi : i ∈ rawVariables Γ C.1 (C.2 j)) :
    i ∈ rawVariables (k :: Γ) C E := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨j, by simp, ?_⟩
  simpa only [if_neg hn] using hi

private theorem head_support (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E : Upper k)
    (a : Nat × Atom k) (ha : a ∈ E.atoms) (j : Fin k) (i : Nat)
    (hi : i ∈ rawVariables Γ C.1 (C.2 j)) :
    i ∈ rawVariables (k :: Γ) C E := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  exact List.mem_flatMap.mpr ⟨j, by simp, hi⟩

private theorem lowerPart_support (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E : Upper k) (i : Nat)
    (hi : i ∈ rawVariables Γ C.1 (lowerPart k Γ C E)) :
    i ∈ rawVariables (k :: Γ) C E := by
  obtain ⟨j, hn, hj⟩ :=
    (mem_rawVariables_combination Γ C.1 k E.constant E.outside C.2 i).mp hi
  exact outside_support k Γ C E j hn i hj

theorem sourceTerms_support (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k)
    (T : Syntax Γ) (hT : T ∈ sourceTerms k Γ C E F) (i : Nat)
    (hi : i ∈ rawVariables Γ C.1 T) : i ∈ sourceAmbient k Γ C E F := by
  rcases List.mem_append.mp hT with hT | hT
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hT
    obtain ⟨j, hn, hj⟩ := (mem_rawVariables_combination Γ C.1 k
      (actualOrdinalNorm a.2.head.1.repr + a.2.offset)
      (fun j => a.2.factors j + 1) C.2 i).mp hi
    rcases List.mem_append.mp ha with he | hf
    · obtain ⟨b, hb, heq⟩ := List.mem_map.mp he
      exact List.mem_append_left _ (head_support k Γ C E b hb j i hj)
    · obtain ⟨b, hb, heq⟩ := List.mem_map.mp hf
      exact List.mem_append_right _ (head_support k Γ C F b hb j i hj)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact List.mem_append_left _ (lowerPart_support k Γ C E i hi)
    · exact List.mem_append_right _ (lowerPart_support k Γ C F i hi)

/-- The support-free default also makes the support inclusion valid outside
the finite label range, without introducing any additional raw variable. -/
theorem sourceTerm_support (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (j i : Nat)
    (hi : i ∈ rawVariables Γ C.1 (sourceTerm k Γ C E F j)) :
    i ∈ sourceAmbient k Γ C E F := by
  by_cases hj : j < (sourceTerms k Γ C E F).length
  · rw [sourceTerm, List.getD_eq_getElem _ _ hj] at hi
    exact sourceTerms_support k Γ C E F _ (List.getElem_mem hj) i hi
  · rw [sourceTerm, List.getD_eq_default _ _ (by omega), rawVariables_numeral] at hi
    cases hi

theorem originalSourceSupport : Targets.OriginalSourceSupport := by
  refine ⟨largeFormula_label_bound, ?_⟩
  intro k Γ C E F desired i hi
  obtain ⟨j, hj, hv⟩ := List.mem_flatMap.mp hi
  exact sourceTerm_support k Γ C E F j i hv

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards.Proof
