module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionSemanticInterface
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaLiteralProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesProof
open CommonHeadExactVariables CommonLayerSyntax CommonLayerComparison BaseFormula

/-- Narrow literal padding proof, with no balanced compiler dependency. -/
theorem padding_truth (xs : List Nat) (ν : Nat → Nat) :
    (BalancedExactVariables.variablesFormula xs).eval ν := by
  unfold BalancedExactVariables.variablesFormula
  apply (BalancedBoxFormula.Proof.conjunction_eval _ ν).mpr
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  rfl

theorem padding_variables (xs : List Nat) (i : Nat) :
    i ∈ (BalancedExactVariables.variablesFormula xs).variables ↔ i ∈ xs := by
  unfold BalancedExactVariables.variablesFormula
  rw [BalancedBoxFormula.Proof.conjunction_variables]
  constructor
  · rintro ⟨p, hp, hi⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have he : i = j := by
      simpa only [Formula.variables, BaseTerm.variables, List.mem_append,
        List.mem_singleton, or_self] using hi
    simpa only [he] using hj
  · intro hi
    refine ⟨.equal (.variable i) (.variable i), List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
    simp only [Formula.variables, BaseTerm.variables, List.mem_append, List.mem_singleton, or_self]

theorem rawTruthAndExactSupport : CommonHeadExactVariablesTargets.RawTruthAndExactSupport := by
  intro heads E F desired
  constructor
  · intro ν
    change ((compile heads E F desired).eval ν ∧
      (BalancedExactVariables.variablesFormula (support heads E F)).eval ν) ↔ _
    exact and_iff_left (padding_truth _ ν)
  · intro i
    change i ∈ (compile heads E F desired).variables ++
      (BalancedExactVariables.variablesFormula (support heads E F)).variables ↔ _
    rw [List.mem_append, padding_variables]
    simp only [support, List.mem_dedup]
    constructor
    · rintro (h | h)
      · exact CommonLayerComparison.Proof.originalSupport heads E F desired i h
      · exact h
    · exact Or.inr

theorem padding_code (xs : List Nat) :
    BalancedExactVariables.variablesCode xs = (BalancedExactVariables.variablesFormula xs).encode := by
  unfold BalancedExactVariables.variablesCode BalancedExactVariables.variablesFormula
  rw [← BalancedBoxFormula.Proof.conjunction_code]
  simp only [List.map_map]
  rfl

theorem literalCodeCalibration : CommonHeadExactVariablesTargets.LiteralCodeCalibration := by
  intro p
  unfold output
  rw [padding_code]
  rfl

theorem actualSourceClause : CommonHeadExactVariablesTargets.ActualSourceClause := by
  intro Γ hΓ E F desired
  rw [literalCodeCalibration]
  constructor
  · intro ν
    rw [(CommonHeadExactVariablesCalibration.literalBaseFormulaCode _).1 ν,
      (rawTruthAndExactSupport _ _ _ _).1 ν,
      CommonHeadClosureDecisionSuppliers.codedComparison Γ hΓ]
    rw [CommonHeadClosureDecisionSuppliers.sourceCalibration Γ E ν,
      CommonHeadClosureDecisionSuppliers.sourceCalibration Γ F ν]
  · intro i
    rw [(CommonHeadExactVariablesCalibration.literalBaseFormulaCode _).2,
      (rawTruthAndExactSupport _ _ _ _).2 i]
    have hlen : (headCodes Γ).length = Γ.length := List.length_map _
    unfold codedVariables
    rw [hlen, CommonLayerSyntax.Proof.commonRoundtrip Γ.length E,
      CommonLayerSyntax.Proof.commonRoundtrip Γ.length F]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesProof
