module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaLiteralProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler.Proof
open BalancedSyntax

/-- Structural induction retains the original pair support under every typed
certificate. In particular, no genuine-source or positivity assumption is
needed to discharge the translated guard's lower-support premise. -/
theorem originalSupportContainment : Targets.OriginalSupportContainment := by
  intro Γ
  induction Γ with
  | nil =>
    intro C E F desired i hi
    change i ∈ (BalancedRawCompiler.baseFormula E F desired).variables at hi
    change i ∈ E.variables ++ F.variables
    unfold BalancedRawCompiler.baseFormula at hi
    split_ifs at hi
    · exact hi
    · exact hi
    · rcases List.mem_append.mp hi with hF | hE
      · exact List.mem_append.mpr (Or.inr hF)
      · exact List.mem_append.mpr (Or.inl hE)
    · cases hi
  | cons k Γ ih =>
    intro C E F desired i hi
    change i ∈ (BalancedBoxFormula.sourceFormula k Γ C E F desired).variables ++
      (BalancedGuardDescent.sourceTranslation k Γ C E F desired
        (fun G H d => typedFormula Γ C.1 G H d)).variables at hi
    rcases List.mem_append.mp hi with hbox | hguard
    · exact (BalancedBoxFormula.Proof.originalSupportAndLiteralCode.2.1
        k Γ C E F desired).2 i hbox
    · exact BalancedGuardDescent.Proof.actualSourceDescent.2 k Γ C E F desired
        (fun G H d => typedFormula Γ C.1 G H d) (ih C.1) i hguard

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler.Proof
