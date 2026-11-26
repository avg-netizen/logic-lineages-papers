module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafTargets
open OriginalNeutralLeaf UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The literal total old leaf is preserved on EVERY raw input. Its original
Context/Object and StepCertificate encoding, malformed cases and output are
unchanged. No fixed window, closure or successful decoding is assumed. -/
def ActualOriginalNeutralLeafRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  ∀ v : List.Vector Nat 4, evaluate (refineInputs p).oldStep v = evaluate p.oldStep v

/-- The concrete guarded AST pays the original factor and zero-guard neutral
bottom law internally, for arbitrary endpoint, window, old leaf and context.
Numerical calibration is not an inference rule. -/
def ActualOriginalNeutralLeafInternalCases : Prop :=
  ∀ (endpoint : Program 6) (window : Program 1) (oldStep : Program 4),
  OriginalConstructorLeaf.OriginalFactor oldStep (refined endpoint window oldStep) ∧
    NeutralBottom endpoint window (refined endpoint window oldStep)

/-- ONE original globally calibrated tuple precedes all source windows and
Gamma. The full original Package, full-output equality and raw neutral law
are proved conclusions. This does not assert canonical quotient component
inversion, neutral arrow computability or whole context-uniform ID1. -/
def ActualOriginalNeutralLeafGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let q := refineInputs p
     (∀ v : List.Vector Nat 4, evaluate q.oldStep v = evaluate p.oldStep v) ∧
     GlobalSourcePackage.InputsCalibrated n arity q ∧
     GlobalSourcePackage.Package n arity
       (GlobalSourcePackage.source q) (GlobalSourcePackage.computability q)
       (GlobalSourcePackage.lift q) ∧
     OriginalConstructorLeaf.OriginalFactor p.oldStep q.oldStep ∧
     NeutralBottom (endpoint p) p.window q.oldStep)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafTargets
