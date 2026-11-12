module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedPathDefinitions
/-- Native equality on ALL numeric states; malformed/rejected cases retained.
No internal source/certificate inference or runtime selection is asserted. -/
def ActualTransitionEquality : Prop := ∀ n arity (p : GlobalSourcePackage.Inputs),
 GlobalSourcePackage.InputsCalibrated n arity p → ∀ state : Nat,
 evaluate p.oldStep (OriginalHereditaryLambda.stateValues
  (evaluate (transition p.base.oldSource) (List.Vector.ofFn ![state]))) =
 evaluate p.oldStep (OriginalHereditaryLambda.stateValues state)
def ActualOutputEquality : Prop := ∀ n arity (p : GlobalSourcePackage.Inputs),
 GlobalSourcePackage.InputsCalibrated n arity p → ∀ v : List.Vector Nat 4,
 evaluate (refined p.base.oldSource p.oldStep) v = evaluate p.oldStep v
def ActualCalibration : Prop := ∀ n arity (p : GlobalSourcePackage.Inputs),
 GlobalSourcePackage.InputsCalibrated n arity p →
 GlobalSourcePackage.InputsCalibrated n arity (refineInputs p)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathTargets
