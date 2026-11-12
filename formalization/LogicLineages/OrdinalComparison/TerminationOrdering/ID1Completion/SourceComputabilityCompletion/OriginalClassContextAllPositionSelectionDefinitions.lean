module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelection
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All-position observer OUTSIDE the active kernel, so it is not discarded
by the kernel's active branch. The key remains the original pre-minimum key. -/
def classTest (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Program 3 :=
  OriginalClassContextAllPositionObserver.classTest p H G W
    (OriginalActiveClassKernel.classTest p H G W P)

/-- Existing rank-observed minimum pipeline applied to the literal new
predicate. This is NOT ActiveKernelMinimum.inputs on that predicate. -/
def inputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : GlobalSourcePackage.Inputs :=
  OriginalActiveObservedClass.inputs p H G W (classTest p H G W P)

/-- Every actual once-minimum output preserves the paired original-key and
rank observation at each actual in-range cutoff. No class-hit premise.
This is not a full-fold, lambda-selection or cross-context cancellation law. -/
def OutputLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed out parameter gamma count cutoff value : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalActiveClassKernel.Domain p H G W seed parameter ⊓
      (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0) ⊓
        (OriginalContextInsertion.lengthGraph count gamma ⊓
          (OriginalContextInsertion.Below cutoff count ⊓
            graph2 (inputs p H G W P).base.oldRepresentative out seed parameter)))).imp
      ((OriginalTransparentMinimum.graph3
          (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
          value cutoff seed parameter).iff
        (OriginalTransparentMinimum.graph3
          (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
          value cutoff out parameter))))

def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  OriginalTransparentMinimum.ClassTestCalibrated n arity P ∧
    (OriginalActiveObservedMinimum.Properties n arity p H G W (classTest p H G W P) ∧
      OutputLaw p H G W P)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelection
