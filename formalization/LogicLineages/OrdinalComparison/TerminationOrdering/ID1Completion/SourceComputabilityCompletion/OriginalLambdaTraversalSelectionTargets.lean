module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionTargets
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion OriginalLambdaTraversalSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Complete all-input equality of the guarded representative, not merely
agreement on typed active source inputs. All original calibration fields
survive the once-transparent, representative-refined raw tuple. -/
def ActualOriginalLambdaTraversalRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (rawData : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity rawData →
  Path.windowCalibrated n window →
  (∀ v : List.Vector Nat 2,
    evaluate (representative rawData window) v = evaluate rawData.oldRepresentative v) ∧
    InternalOriginalUniformDescentSelection.Calibrated n arity (preparedData rawData window)

/-- Literal AST identities identify the ACTUAL final data with the generic
arbitrary-representative validity bridge, and its actual source with the
acyclic leaf supplier's source. Native evaluation is not used for transport. -/
def ActualOriginalLambdaTraversalSelectionIdentity : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  (finalInputs p).window = p.window ∧
    finalData p = OriginalTransparentLambdaFinal.selectedData p.base
      (finalInputs p).base.oldRepresentative p.window ∧
    InternalOriginalUniformDescentSelection.validity (finalData p) =
      InternalOriginalUniformDescentSelection.validity (leafData p.base p.window) ∧
    (finalData p).member = (leafData p.base p.window).member

/-- Internal supporting facts for arbitrary original Program tuples, with
only actual source/window/type/fold graphs in their arithmetic antecedents. -/
def ActualOriginalLambdaTraversalOutputLaws : Prop :=
  ∀ (rawData : Data) (window : Program 1), OutputLaws rawData window

def ActualOriginalLambdaTraversalObserverLaws : Prop :=
  ∀ (rawData : Data) (window : Program 1), ObserverLaws rawData window

def ActualOriginalLambdaTraversalFinalTransition : Prop :=
  ∀ p : GlobalSourcePackage.Inputs, FinalTransitionLaw p

def ActualOriginalLambdaTraversalFinalCanonical : Prop :=
  ∀ p : GlobalSourcePackage.Inputs, FinalCanonicalLaw p

def ActualOriginalLambdaTraversalFinalBodyFixed : Prop :=
  ∀ p : GlobalSourcePackage.Inputs, FinalBodyFixedLaw p

def ActualOriginalLambdaTraversalFinalLambdaEquation : Prop :=
  ∀ p : GlobalSourcePackage.Inputs, FinalLambdaEquation p

/-- Native preparation is separate from every internal graph theorem. -/
def ActualOriginalLambdaTraversalNativePreparation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p → NativePreparation n arity p

/-- ONE globally calibrated original tuple, chosen before every source
window and runtime Gamma, retains the ENTIRE preceding Package with the new
SAME-final laws. No internal source/body/canonical supplier is a premise. -/
def ActualOriginalLambdaTraversalGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ p : GlobalSourcePackage.Inputs,
      GlobalSourcePackage.InputsCalibrated n arity p ∧ Properties n arity p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionTargets
