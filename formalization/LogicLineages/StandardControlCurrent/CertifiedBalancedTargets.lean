module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionWorkingDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CertifiedBalancedTargets
open OrdinalComparison LayeredComparison LayeredComparison.SnyatkovCompletion SixSol20261112

/-- Literal operations in one shared lower certificate, including signed
rows whose head blocks cancel completely. This supports the main comparison. -/
def LowerCertificateClosure : Prop :=
  BalancedSyntax.Affine.Targets.LiteralAffineClosure ∧
  BalancedSyntax.Affine.Targets.ExactAffineSupport ∧
  BalancedSyntax.Affine.Targets.ActualLowerAndInputs ∧
  BalancedSyntax.Affine.Targets.ActualCanceledDescent

/-- The three signs of the same whole certified pair, a literal computed
base formula and its exactly retained original free-name membership. -/
def ExactPointwise : Prop :=
  BalancedExactVariables.Targets.TruthAndExactVariables ∧
  BalancedExactVariables.Targets.ActualSignSemantics ∧
  BalancedExactVariables.Targets.ExactTypedCodeCalibration ∧
  BalancedExactVariables.Targets.AllCodeComputation

/-- Whole pair certificates, actual positive free-name domain, literal
positive binders/duals and original shadowing survive in-place translation. -/
def ExactTranslation : Prop :=
  BalancedFirstOrderTargets.ActualSourceTranslation ∧
  BalancedFirstOrderTargets.ExactFreeVariables ∧
  BalancedFirstOrderTargets.LiteralCodeCalibration ∧
  BalancedFirstOrderTargets.ActualNumericProgram ∧
  BalancedFirstOrderTargets.ExactUniversalDomain

/-- Concrete total composition with the actual fixed-control decision. Every
certified closed balanced formula and every starting valuation is covered;
positivity of bound names is enforced by the original positive domains. -/
def ActualClosedAnswer : Prop :=
  Computable (fun code : Nat => SourceDecision.answer (BalancedFirstOrder.Code.translate code)) ∧
  (∀ p : BalancedFirstOrder.Formula,
    SourceDecision.answer (BalancedFirstOrder.Code.translate p.encode) =
      SourceDecision.answer (BalancedFirstOrder.translate p).encode) ∧
  ∀ p : BalancedFirstOrder.Formula, p.certified → p.variables = [] → ∀ ν : Nat → Nat,
    SourceDecision.answer (BalancedFirstOrder.Code.translate p.encode) = true ↔ p.eval ν

/-- Paper18 m:thm:balanced, certified-fragments.tex 181–186, including
effective pointwise comparison and full certified closed-sentence decision. -/
def FullBalancedComparison : Prop := ExactPointwise ∧ ExactTranslation ∧ ActualClosedAnswer

end LogicLineages.StandardControlCurrent.CertifiedBalancedTargets
