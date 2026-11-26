module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalClassContextAllPositionObserver
/-- Native-only all-vector equality. Not an arithmetic inference principle. -/
def Calibration : Prop :=
  ∀ n (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalTransparentMinimum.ClassTestCalibrated n arity (classTest p H G W P)
/-- Internal exposure of the SAME finite observer at any actually in-range
cutoff. The paired output contains both key and rank. No class/coherence,
source validity, native equality, or desired observation is a premise. -/
def Hit : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed candidate parameter gamma count cutoff value : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (OriginalActiveObservedClass.activation p H G W)
        InternalOriginalStepGuard.one seed parameter ⊓
      (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0) ⊓
      (OriginalContextInsertion.lengthGraph count gamma ⊓
      (OriginalContextInsertion.Below cutoff count ⊓
       OriginalTransparentMinimum.graph3 (classTest p H G W P)
         InternalOriginalStepGuard.one seed candidate parameter)))).imp
     ((OriginalTransparentMinimum.graph3 (positionObservation p.base.oldRepresentative)
       value cutoff seed parameter).iff
      (OriginalTransparentMinimum.graph3 (positionObservation p.base.oldRepresentative)
       value cutoff candidate parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverTargets
