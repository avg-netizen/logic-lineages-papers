module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeTargets
open OriginalVariableRepresentative UniformCertificateCompletion
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal equality at EVERY raw value/parameter pair, including malformed,
inactive, rejected, nonclosed-window and packed-target fallback inputs. The
original Data calibration and globally selected window calibration are the
only premises. The resulting Data calibration is proved, not assumed. -/
def ActualOriginalVariableRepresentativeRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  Path.windowCalibrated n window →
  (∀ v : List.Vector Nat 2,
    evaluate (representative data window) v = evaluate data.oldRepresentative v) ∧
  InternalOriginalUniformDescentSelection.Calibrated n arity (baseData data window)

/-- No native calibration hypothesis or stored correctness field is an
internal rule. Both selected bounded-descent preservation AND actual full
canonical-fold rigidity must be derived from the same literal guarded Data.
Do not weaken the second conclusion to oldR preservation or forward fixedness. -/
def ActualOriginalSelectedVariableRepresentativeRigidity : Prop :=
  ∀ (data : Data) (window : Program 1),
    SelectedMarkPreservation (selectedData data window) window ∧
    FullFoldRigidity (selectedData data window) window

/-- ONE final globally constructed source precedes ALL windows and Gamma.
Original step equality, original acceptance factor and constructor cases are
retained at the SAME once-refined oldStep. No independent existential source,
representative oracle, path inversion assumption or new certificate encoding
is supplied. The original full R005 package and the actual full-fold rigidity
are conclusions. Nonapplication peel/repeat and path induction remain open. -/
def ActualOriginalVariableRepresentativeGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let r := refineInputs p
     (∀ v : List.Vector Nat 4, evaluate r.oldStep v = evaluate p.oldStep v) ∧
     (∀ v : List.Vector Nat 2,
       evaluate r.base.oldRepresentative v = evaluate p.base.oldRepresentative v) ∧
     GlobalSourcePackage.InputsCalibrated n arity r ∧
     GlobalSourcePackage.Package n arity
       (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
       (GlobalSourcePackage.lift r) ∧
     OriginalConstructorLeaf.OriginalFactor p.oldStep r.oldStep ∧
     OriginalConstructorLeaf.ConstructorCases r.oldStep ∧
     SelectedMarkPreservation (OuterSelection.data r.base r.window) r.window ∧
     FullFoldRigidity (OuterSelection.data r.base r.window) r.window)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeTargets
