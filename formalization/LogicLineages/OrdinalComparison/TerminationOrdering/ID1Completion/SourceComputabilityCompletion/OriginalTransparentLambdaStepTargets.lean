module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open OriginalTransparentLambdaStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All vectors, including malformed source/context/target/certificate.
Native calibration is used only here, never as an internal inference rule. -/
def ActualOriginalTransparentLambdaStepEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  ∀ v : List.Vector Nat 4, evaluate (refineInputs p).oldStep v = evaluate p.oldStep v

def ActualOriginalTransparentLambdaStepCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  GlobalSourcePackage.InputsCalibrated n arity (refineInputs p)

/-- SAME normalized checker at both endpoints of one original lambda-prefix
hop, for ANY result and arbitrary oldStep. This is an internal graph equality,
not native reflection or a claim about full effective wrapper acceptance. -/
def ActualOriginalTransparentLambdaStepHop : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter childS childT childCert childParam d e context gamma extended out : OTerm alpha),
  Nonempty (Derivation body Delta
    ((LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended).imp
      ((graph4 (refined source oldStep) out s t cert parameter).iff
        (graph4 (refined source oldStep) out childS childT childCert childParam))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepTargets
