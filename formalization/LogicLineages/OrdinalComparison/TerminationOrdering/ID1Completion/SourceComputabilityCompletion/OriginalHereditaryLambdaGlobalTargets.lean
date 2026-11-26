module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalTargets
open UniformCertificateCompletion OriginalHereditaryLambdaGlobal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Arbitrary original endpoint, window and oldStep Programs. The conclusion
recovers the SAME entire effective leaf at the actual lambda body selectors,
stripped certificate and extended parameter, preserving the exact prefix
graph. It has no native calibration, source typing, window membership,
external witness, fuel bound or source-closure premise. -/
def ActualOriginalHereditaryLambdaGlobalInternalClosure : Prop :=
  ∀ (endpoint : Program 6) (window : Program 1) (oldStep : Program 4),
    OriginalHereditaryLambda.InternalChildElimination (closedLeaf endpoint window oldStep)

/-- Calibrate the inner priorFinal leaf BEFORE hereditary refinement, then
the prepared input and unchanged final pipeline. Both structural equations
are literal Program identities, not internal graph transport by evaluation.
The resulting all-input native equalities are separately recorded and cannot
serve as an arithmetic inference rule in the closure contract above. -/
def ActualOriginalHereditaryLambdaGlobalPreparation : Prop :=
  (∀ p : GlobalSourcePackage.Inputs,
    (priorFinal p).oldStep = wrapper (endpoint p) p.window p.oldStep ∧
      endpoint (prepareInputs p) = endpoint p ∧
      (finalInputs p).oldStep = closedLeaf (endpoint p) p.window p.oldStep) ∧
  (∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
    GlobalSourcePackage.InputsCalibrated n arity p → NativePreparation n arity p)

/-- ONE globally calibrated original tuple precedes every source window,
runtime Gamma, finite type and internal derivation. Its complete previously
accepted package and every child/suffix/neutral/variable consumer coexist
with hereditary child closure of the SAME ACTUAL effective final oldStep.
No source relation is replaced, and ordinary/quotient body-edge closure or
whole lambda/substitution computability is not asserted. -/
def ActualOriginalHereditaryLambdaGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ p : GlobalSourcePackage.Inputs,
      GlobalSourcePackage.InputsCalibrated n arity p ∧ Properties n arity p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalTargets
