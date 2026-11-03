module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Proof
open BalancedSyntax BaseFormula CommonLayerSyntax

/-- Literal reflexive equalities are true at every raw valuation, including
zero coordinates. The empty support uses the existing true conjunction tail. -/
theorem variablesFormula_eval (support : List Nat) (ν : Nat → Nat) :
    (variablesFormula support).eval ν := by
  unfold variablesFormula
  apply (BalancedBoxFormula.Proof.conjunction_eval _ ν).mpr
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  rfl

/-- The padding mentions exactly its actual raw variable names. Membership,
rather than list equality, ignores the two occurrences in each equality. -/
theorem variablesFormula_variables (support : List Nat) (i : Nat) :
    i ∈ (variablesFormula support).variables ↔ i ∈ support := by
  unfold variablesFormula
  rw [BalancedBoxFormula.Proof.conjunction_variables]
  constructor
  · rintro ⟨p, hp, hi⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have he : i = j := by
      simpa only [Formula.variables, BaseTerm.variables, List.mem_append,
        List.mem_singleton, or_self] using hi
    simpa only [he] using hj
  · intro hi
    refine ⟨.equal (.variable i) (.variable i),
      List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
    simp only [Formula.variables, BaseTerm.variables, List.mem_append,
      List.mem_singleton, or_self]

/-- The accepted comparison is retained literally. Its support containment
pays the forward direction, and the original-support padding pays the reverse
direction even when cancellation or an impossible sign makes it constant. -/
theorem truthAndExactVariables : Targets.TruthAndExactVariables := by
  intro Γ C E F desired
  constructor
  · intro ν
    change ((BalancedTypedCompiler.typedFormula Γ C E F desired).eval ν ∧
      (variablesFormula (sourceSupport Γ C E F)).eval ν) ↔
        (BalancedTypedCompiler.typedFormula Γ C E F desired).eval ν
    constructor
    · exact And.left
    · intro h
      exact ⟨h, variablesFormula_eval _ ν⟩
  · intro i
    change i ∈ (BalancedTypedCompiler.typedFormula Γ C E F desired).variables ++
      (variablesFormula (sourceSupport Γ C E F)).variables ↔
        i ∈ BalancedSyntax.rawVariables Γ C E ++ BalancedSyntax.rawVariables Γ C F
    rw [List.mem_append, variablesFormula_variables]
    simp only [sourceSupport, List.mem_dedup]
    constructor
    · rintro (hcomparison | hpadding)
      · exact BalancedTypedCompiler.Proof.originalSupportContainment
          Γ C E F desired i hcomparison
      · exact hpadding
    · exact Or.inr

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Proof
