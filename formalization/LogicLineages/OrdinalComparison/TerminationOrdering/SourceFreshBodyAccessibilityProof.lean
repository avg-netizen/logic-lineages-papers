module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFreshBodyAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFreshBodyAccessibilityProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths SourceFreshBodyAccessibility

theorem actualFreshBodyIdentity : SourceFreshBodyAccessibilityTargets.ActualFreshBodyIdentity := by
  intro Symbol arity Gamma sigma tau body
  exact NumberedRewriteApplicationBindingProof.bindingRetraction Symbol arity (sigma :: Gamma) (sigma :: sigma :: Gamma)
    (Renaming.lift (Renaming.weaken Gamma sigma)) (singleSubstitution (.var .here))
    (by intro upsilon v; cases v <;> rfl) tau body

theorem actualFreshBodyAccessibility : SourceFreshBodyAccessibilityTargets.ActualFreshBodyAccessibility := by
  intro n arity Gamma context ctx scalar hc hclosed sigma hcal tau body hcomp
  rw [actualFreshBodyIdentity (Fin n) arity Gamma sigma tau body] at hcomp
  have hacc := SourceComputabilityLeastProof.actualComputabilityAccessible n arity (sigma :: Gamma) context ctx scalar
    hc hclosed hcal tau _ hcomp
  exact Subrelation.accessible (fun {y x} h =>
    (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity (sigma :: Gamma) context ctx hc x y).mpr h) hacc

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFreshBodyAccessibilityProof
