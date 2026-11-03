module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxProof
public import Mathlib.Data.List.GetD
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Proof
open BaseFormula CommonLayerSyntax

/-- Literal Boolean folds have their ordinary finite-list truth conditions. -/
theorem conjunction_eval (ps : List Formula) (ν : Nat → Nat) :
    (conjunction ps).eval ν ↔ ∀ p ∈ ps, p.eval ν := by
  induction ps with
  | nil => simp [conjunction, Formula.eval]
  | cons p ps ih =>
    change (p.eval ν ∧ (conjunction ps).eval ν) ↔ _
    rw [ih]
    simp

theorem disjunction_eval (ps : List Formula) (ν : Nat → Nat) :
    (disjunction ps).eval ν ↔ ∃ p ∈ ps, p.eval ν := by
  induction ps with
  | nil => simp [disjunction, Formula.eval]
  | cons p ps ih =>
    change (p.eval ν ∨ (disjunction ps).eval ν) ↔ _
    rw [ih]
    simp

/-- Every coordinate tests the original raw name against its literal numeral. -/
theorem point_eval (support word : List Nat) (ν : Nat → Nat) :
    (pointFormula support word).eval ν ↔
      ∀ j < support.length, ν (support.getD j 0) = word.getD j 1 := by
  unfold pointFormula
  rw [conjunction_eval]
  constructor
  · intro h j hj
    exact h _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  · intro h p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    exact h j (List.mem_range.mp hj)

/-- On a word of the required length, point truth determines the entire word.
This statement does not assume positivity, distinct names, or outside values. -/
theorem point_eval_iff_map (support word : List Nat) (ν : Nat → Nat)
    (hlen : word.length = support.length) :
    (pointFormula support word).eval ν ↔ word = support.map ν := by
  constructor
  · intro hp
    apply List.ext_getElem
    · simpa only [List.length_map] using hlen
    · intro j hj hj'
      have hs : j < support.length := by simpa only [hlen] using hj
      have he := (point_eval support word ν).mp hp j hs
      rw [List.getD_eq_getElem support 0 hs, List.getD_eq_getElem word 1 hj] at he
      simpa only [List.getElem_map] using he.symm
  · intro hw
    subst word
    apply (point_eval support (support.map ν) ν).mpr
    intro j hj
    rw [List.getD_eq_getElem support 0 hj,
      List.getD_eq_getElem (support.map ν) 1 (by simpa only [List.length_map] using hj),
      List.getElem_map]

/-- These are equalities of the existing postfix instruction lists. -/
theorem conjunction_code (ps : List Formula) :
    CommonHeadCode.conjoin (ps.map Formula.encode) = (conjunction ps).encode := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change CommonHeadCode.conjunction p.encode
      (CommonHeadCode.conjoin (ps.map Formula.encode)) =
        (Formula.conjunction p (conjunction ps)).encode
    rw [ih]
    rfl

theorem disjunction_code (ps : List Formula) :
    CommonHeadCode.disjoin (ps.map Formula.encode) = (disjunction ps).encode := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change CommonHeadCode.disjunction p.encode
      (CommonHeadCode.disjoin (ps.map Formula.encode)) =
        (Formula.disjunction p (disjunction ps)).encode
    rw [ih]
    rfl

theorem point_code (support word : List Nat) :
    pointCode support word = (pointFormula support word).encode := by
  unfold pointCode pointFormula
  rw [← conjunction_code]
  simp only [List.map_map]
  rfl

theorem points_code (support : List Nat) (words : List (List Nat)) :
    CommonHeadCode.disjoin (words.map (pointCode support)) =
      (disjunction (words.map (pointFormula support))).encode := by
  rw [← disjunction_code]
  apply congrArg CommonHeadCode.disjoin
  rw [List.map_map]
  apply List.map_congr_left
  intro word hword
  exact point_code support word

/-- Every raw output is already the code of a literal finite-point formula. -/
theorem formula_code_literal (k : Nat) (Γ : List Nat) (C E F : Nat)
    (desired : Int) :
    formulaCode k Γ C E F desired =
      (disjunction (((rawWords k Γ C E F).filter (fun word =>
        decide (codeSign (k :: Γ) C E F (rawSupport k Γ C E F) word = desired))).map
          (pointFormula (rawSupport k Γ C E F)))).encode := by
  unfold formulaCode
  exact points_code _ _

private theorem raw_variables_append (xs ys : Code) :
    BaseFormula.rawVariables (xs ++ ys) =
      BaseFormula.rawVariables xs ++ BaseFormula.rawVariables ys := by
  simp only [BaseFormula.rawVariables, GuardCodeRuntime.codeVariables, List.flatMap_append]

/-- Reproved directly for literal constructors, without the broad runtime or
compiler proof imports. Atomic decoding uses the accepted BaseTerm round trip. -/
theorem raw_variables_encode (p : Formula) :
    BaseFormula.rawVariables p.encode = p.variables := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | equal E F =>
    simp [BaseFormula.rawVariables, Formula.encode, Formula.guardView,
      CommonHeadCompiler.encode, GuardCodeRuntime.codeVariables,
      Formula.variables]
    rw [CommonLayerSyntax.Proof.baseRoundtrip E, CommonLayerSyntax.Proof.baseRoundtrip F]
  | less E F =>
    simp [BaseFormula.rawVariables, Formula.encode, Formula.guardView,
      CommonHeadCompiler.encode, GuardCodeRuntime.codeVariables,
      Formula.variables]
    rw [CommonLayerSyntax.Proof.baseRoundtrip E, CommonLayerSyntax.Proof.baseRoundtrip F]
  | negative p ih =>
    change BaseFormula.rawVariables (p.encode ++ [(5, 0, 0)]) = p.variables
    rw [raw_variables_append, ih]
    exact List.append_nil _
  | conjunction p q ihp ihq =>
    change BaseFormula.rawVariables (p.encode ++ q.encode ++ [(6, 0, 0)]) =
      p.variables ++ q.variables
    rw [raw_variables_append, raw_variables_append, ihp, ihq]
    exact List.append_nil _
  | disjunction p q ihp ihq =>
    change BaseFormula.rawVariables (p.encode ++ q.encode ++ [(7, 0, 0)]) =
      p.variables ++ q.variables
    rw [raw_variables_append, raw_variables_append, ihp, ihq]
    exact List.append_nil _

theorem conjunction_variables (ps : List Formula) (i : Nat) :
    i ∈ (conjunction ps).variables ↔ ∃ p ∈ ps, i ∈ p.variables := by
  induction ps with
  | nil => simp [conjunction, Formula.variables]
  | cons p ps ih =>
    change i ∈ p.variables ++ (conjunction ps).variables ↔ _
    rw [List.mem_append, ih]
    simp

theorem disjunction_variables (ps : List Formula) (i : Nat) :
    i ∈ (disjunction ps).variables ↔ ∃ p ∈ ps, i ∈ p.variables := by
  induction ps with
  | nil => simp [disjunction, Formula.variables]
  | cons p ps ih =>
    change i ∈ p.variables ++ (disjunction ps).variables ↔ _
    rw [List.mem_append, ih]
    simp

theorem point_variables (support word : List Nat) (i : Nat)
    (hi : i ∈ (pointFormula support word).variables) : i ∈ support := by
  unfold pointFormula at hi
  obtain ⟨p, hp, hi⟩ := (conjunction_variables _ i).mp hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  have he : i = support.getD j 0 := by
    simpa only [Formula.variables, BaseTerm.variables, List.append_nil,
      List.mem_singleton] using hi
  rw [he, List.getD_eq_getElem support 0 (List.mem_range.mp hj)]
  exact List.getElem_mem _

theorem originalSupportAndLiteralCode : Targets.OriginalSupportAndLiteralCode := by
  refine ⟨point_code, ?_, ?_⟩
  · intro k Γ C E F desired
    refine ⟨raw_variables_encode _, ?_⟩
    intro i hi
    unfold sourceFormula at hi
    obtain ⟨p, hp, hi⟩ := (disjunction_variables _ i).mp hi
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hp
    have hs := point_variables (BalancedSmallBox.sourceSupport k Γ C E F) word i hi
    simpa only [BalancedSmallBox.sourceSupport, List.mem_dedup] using hs
  · intro k Γ C E F desired i hi
    unfold formulaCode at hi
    rw [points_code, raw_variables_encode] at hi
    obtain ⟨p, hp, hi⟩ := (disjunction_variables _ i).mp hi
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hp
    exact point_variables (rawSupport k Γ C E F) word i hi

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Proof
