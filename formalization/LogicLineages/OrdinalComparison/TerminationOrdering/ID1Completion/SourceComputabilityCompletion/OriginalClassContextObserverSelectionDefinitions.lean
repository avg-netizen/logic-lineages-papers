module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelection
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Insert the erasure observer OUTSIDE the active kernel, so the kernel
cannot discard it when selecting its active branch. -/
def classTest (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Program 3 :=
  OriginalClassContextObserver.classTest p H G W
    (OriginalActiveClassKernel.classTest p H G W P)
/-- Apply the existing rank observer/minimum pipeline to that exact predicate.
Do not call OriginalActiveKernelMinimum.inputs on the observer predicate. -/
def inputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : GlobalSourcePackage.Inputs :=
  OriginalActiveObservedClass.inputs p H G W (classTest p H G W P)
/-- Actual output of the once-guarded minimum preserves both erased observers
at this same original nonempty context. Reflexive hits are handled internally;
no class-hit premise is imposed on the output. This is not full-fold transport. -/
def OutputLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed out parameter gamma tail key rank : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalActiveClassKernel.Domain p H G W seed parameter ⊓
      (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0) ⊓
        ((equal gamma (OrdinaryArithmetic.succTerm tail)) ⊓
          graph2 (inputs p H G W P).base.oldRepresentative out seed parameter))).imp
      (((graph2 (OriginalClassContextObserver.erasedKey p.base.oldRepresentative)
          key seed parameter).iff
        (graph2 (OriginalClassContextObserver.erasedKey p.base.oldRepresentative)
          key out parameter)) ⊓
        ((graph2 OriginalClassContextObserver.erasedRank rank seed parameter).iff
          (graph2 OriginalClassContextObserver.erasedRank rank out parameter)))))
def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  OriginalTransparentMinimum.ClassTestCalibrated n arity P ∧
    (OriginalActiveObservedMinimum.Properties n arity p H G W (classTest p H G W P) ∧
      OutputLaw p H G W P)
/- Coherence/idempotence of this new observed minimum, full-fold erasure
compatibility, cross-context cancellation, internal I/C remain separate. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelection
