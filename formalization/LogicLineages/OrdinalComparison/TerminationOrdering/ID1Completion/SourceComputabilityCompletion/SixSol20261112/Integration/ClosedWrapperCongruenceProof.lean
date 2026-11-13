module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OperatorCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedWrapperCongruenceProof
open InternalControlGraph
open GraphCongruenceProof OperatorCongruenceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] ProgramGraphEquivalent programGraph

theorem endpointGuard {p q : Program 6} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent
      (InternalParameterizedApplicationStepChecker.endpointGuardP p)
      (InternalParameterizedApplicationStepChecker.endpointGuardP q) := by
  unfold InternalParameterizedApplicationStepChecker.endpointGuardP
  exact conjunctionCongruence (equivalentRefl _) hp

theorem endpointAt {p q : Program 6} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent
      (InternalParameterizedApplicationStepChecker.endpointAtP p)
      (InternalParameterizedApplicationStepChecker.endpointAtP q) := by
  unfold InternalParameterizedApplicationStepChecker.endpointAtP
    InternalParameterizedApplicationResultStack.wireP
  exact postcompose (endpointGuard hp) _

theorem guard {p q : Program 6} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent
      (InternalParameterizedApplicationStepChecker.guardP p)
      (InternalParameterizedApplicationStepChecker.guardP q) := by
  unfold InternalParameterizedApplicationStepChecker.guardP
  exact conjunctionCongruence (equivalentRefl _) (endpointAt hp)

theorem guardAt {p q : Program 6} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalNeutralLeaf.guardAt p)
      (OriginalNeutralLeaf.guardAt q) := by
  unfold OriginalNeutralLeaf.guardAt
  exact postcompose (guard hp) _

theorem trigger {p q : Program 6} (hp : ProgramGraphEquivalent p q) (window : Program 1) :
    ProgramGraphEquivalent (OriginalNeutralLeaf.trigger p window)
      (OriginalNeutralLeaf.trigger q window) := by
  unfold OriginalNeutralLeaf.trigger
  exact conjunctionCongruence (equivalentRefl _)
    (conjunctionCongruence (equivalentRefl _)
      (sameCongruence (guardAt hp) (equivalentRefl _)))

theorem leafGuard {p q : Program 6} (hp : ProgramGraphEquivalent p q) (window : Program 1) :
    ProgramGraphEquivalent (OriginalNeutralLeaf.leafGuard p window)
      (OriginalNeutralLeaf.leafGuard q window) := by
  unfold OriginalNeutralLeaf.leafGuard
  exact branchCongruence (trigger hp window) (equivalentRefl _) (equivalentRefl _)

/-- Each original wrapper factor is retained at every output. Fixed tests
are used once as opaque original Programs, rather than expanded arithmetic. -/
theorem wrapper {p q : Program 6} (hp : ProgramGraphEquivalent p q)
    {leaf other : Program 4} (hl : ProgramGraphEquivalent leaf other) (window : Program 1) :
    ProgramGraphEquivalent (OriginalHereditaryLambdaGlobal.wrapper p window leaf)
      (OriginalHereditaryLambdaGlobal.wrapper q window other) := by
  unfold OriginalHereditaryLambdaGlobal.wrapper OriginalConstructorLeaf.refined
    OriginalNeutralLeaf.refined OriginalSpineGuardLeaf.refined
  exact conjunctionCongruence
    (conjunctionCongruence
      (conjunctionCongruence hl (equivalentRefl _)) (leafGuard hp window))
    (equivalentRefl _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedWrapperCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedWrapperCongruenceProof
