module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentApplicationFunctionDefinitions
/-- All native vectors and both Boolean outcomes. Genuine calibrated source
validity pays the function/argument decoding; target need not be in the universe. -/
def ActualGuardedEquality : Prop := ∀ n arity (p : GlobalSourcePackage.Inputs),
 GlobalSourcePackage.InputsCalibrated n arity p → ∀ v : List.Vector Nat 4,
 evaluate (hopGuard p.base.oldSource) v = 1 →
 evaluate p.oldStep (List.Vector.ofFn ![evaluate sourceFunction v,evaluate targetFunction v,
  evaluate childCertificate v,v.get 3]) = evaluate p.oldStep v
/-- Entire state, all values including rejected/malformed cases. Native only. -/
def ActualTransitionEquality : Prop := ∀ n arity (p : GlobalSourcePackage.Inputs),
 GlobalSourcePackage.InputsCalibrated n arity p → ∀ state : Nat,
 evaluate p.oldStep (OriginalHereditaryLambda.stateValues
  (evaluate (transition p.base.oldSource) (List.Vector.ofFn ![state]))) =
 evaluate p.oldStep (OriginalHereditaryLambda.stateValues state)
def ActualOneStepEquality : Prop := ∀ n arity (p : GlobalSourcePackage.Inputs),
 GlobalSourcePackage.InputsCalibrated n arity p → ∀ v : List.Vector Nat 4,
 evaluate (oneStep p.base.oldSource p.oldStep) v = evaluate p.oldStep v
def ActualCalibration : Prop := ∀ n arity (p : GlobalSourcePackage.Inputs),
 GlobalSourcePackage.InputsCalibrated n arity p →
 GlobalSourcePackage.InputsCalibrated n arity (refineInputs p)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionTargets
