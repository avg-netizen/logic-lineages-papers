module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionSupplierTargets
open BalancedSyntax BalancedEvaluation

/-- Exact existing raw support helper, with the unchanged original pair. -/
def OriginalSupportCalibration : Prop := ∀ (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ),
  BalancedExactVariables.rawSupport Γ (encodeCertificate Γ C) (encodeSyntax Γ E) (encodeSyntax Γ F) =
    BalancedExactVariables.sourceSupport Γ C E F

/-- Exact existing support algorithm, uniformly on the raw compiler input. -/
def OriginalSupportComputation : Prop := Computable (fun a : BalancedRawCompiler.Input =>
  BalancedExactVariables.rawSupport a.1 a.2.1 a.2.2.1 a.2.2.2.1)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionSupplierTargets
