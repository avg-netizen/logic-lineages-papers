module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerCallProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler.Proof
open BalancedSyntax BalancedEvaluation

/-- The structural typed formula has exactly the accepted raw compiler's
literal code on every typed input. The induction calibrates every original
child, including ignored Boolean children, under the unchanged lower C.1. -/
theorem exactTypedCodeCalibration : Targets.ExactTypedCodeCalibration := by
  intro Γ
  induction Γ with
  | nil =>
    intro C E F desired
    exact (BalancedRawCompiler.Proof.exactFiniteCallEquation.2.1
      (encodeCertificate [] C) E F desired).1
  | cons k Γ ih =>
    intro C E F desired
    let lower : BalancedGuardDescent.Lower Γ := typedFormula Γ C.1
    obtain ⟨hchildren, hassemble⟩ :=
      BalancedGuardDescent.Proof.exactActualCallsAndDescent.2
        k Γ C E F desired lower
    have hresults :
        (BalancedGuardDescent.sourceChildren k Γ (encodeCertificate (k :: Γ) C)
          (encodeSyntax (k :: Γ) E) (encodeSyntax (k :: Γ) F) desired).map
            (fun a => BalancedRawCompiler.compileCode Γ
              a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) =
          BalancedGuardDescent.typedResults Γ lower
            (BalancedLargeGuards.sourceTerms k Γ C E F)
            (CommonHeadCompiler.encode (BalancedLargeGuards.sourceFormula E F desired)) := by
      rw [hchildren]
      simp only [List.map_map, BalancedGuardDescent.typedResults, Function.comp_def]
      apply List.map_congr_left
      intro q hq
      exact ih C.1 _ _ _
    have hbox := (BalancedBoxFormula.Proof.actualSourceCodeCalibration
      k Γ C E F desired).2.2.2.2
    rw [BalancedRawCompiler.compileCode, typedFormula, hresults, hassemble, hbox]
    rfl

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler.Proof
