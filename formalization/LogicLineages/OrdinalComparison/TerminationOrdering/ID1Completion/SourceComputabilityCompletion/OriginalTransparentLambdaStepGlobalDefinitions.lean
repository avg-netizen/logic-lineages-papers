module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepWrapperTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGlobal
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Normalize the WHOLE already calibrated original inner effective leaf.
The original source is retained literally, independently of later validators. -/
def prepared (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := OriginalTransparentLambdaStep.refined p.base.oldSource (OriginalHereditaryLambdaGlobal.priorFinal p).oldStep }

def selected (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : GlobalSourcePackage.Inputs :=
  OriginalActiveKernelMinimum.inputs (prepared p) H G W P

/-- Exactly ONE variable refinement, matching the retained rank package. -/
def refined (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : GlobalSourcePackage.Inputs :=
  OriginalVariableLeaves.refineInputs G (selected p H G W P)

def finalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : GlobalSourcePackage.Inputs :=
  OriginalLambdaTraversalSelection.finalInputs (refined p H G W P)

/-- Literal AST bridge; no numerical equality transports an internal law. -/
def LiteralLeaf (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let r := refined p H G W P
  (finalInputs p H G W P).oldStep =
    OriginalHereditaryLambdaGlobal.closedLeaf
      (OriginalHereditaryLambdaGlobal.endpoint (OriginalLambdaTraversalSelection.prepareInputs r))
      r.window (OriginalTransparentLambdaStep.refined p.base.oldSource
        (OriginalHereditaryLambdaGlobal.priorFinal p).oldStep)

/-- Complete native outputs, including rejected/malformed vectors. -/
def NativePreparation (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity (prepared p) ∧
    GlobalSourcePackage.InputsCalibrated n arity (refined p H G W P) ∧
    GlobalSourcePackage.InputsCalibrated n arity (finalInputs p H G W P) ∧
    (∀ v : List.Vector Nat 4,
      evaluate (prepared p).oldStep v = evaluate p.oldStep v ∧
      evaluate (refined p H G W P).oldStep v = evaluate p.oldStep v ∧
      evaluate (finalInputs p H G W P).oldStep v = evaluate p.oldStep v)

/-- Child and parent use the SAME actual final checker. The original parent
source graph is explicit; it is NOT inferred from child acceptance. No final
canonical/source-edge/quotient or erasure conclusion is asserted. -/
def FinalIntroduction (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let leaf := (finalInputs p H G W P).oldStep
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter childS childT childCert childParam d e context gamma extended : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalTransparentLambdaStep.LambdaHop p.base.oldSource
      s t cert parameter childS childT childCert childParam d e context gamma extended ⊓
      graph4 leaf InternalOriginalStepGuard.one childS childT childCert childParam).imp
      (graph4 leaf InternalOriginalStepGuard.one s t cert parameter)))

/-- The entire prior kernel/minimum package and the new literal final
supplier coexist at one prepared tuple. This is not internal I/C completion. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  NativePreparation n arity p H G W P ∧
    OriginalActiveKernelMinimum.Properties n arity (prepared p) H G W P ∧
    LiteralLeaf p H G W P ∧ FinalIntroduction p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGlobal
