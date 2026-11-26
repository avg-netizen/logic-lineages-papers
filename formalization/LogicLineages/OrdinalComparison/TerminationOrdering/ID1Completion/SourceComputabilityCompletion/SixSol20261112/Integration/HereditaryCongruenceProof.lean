module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OperatorCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.HereditaryCongruenceProof
open InternalControlGraph
open GraphCongruenceProof OperatorCongruenceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] ProgramGraphEquivalent programGraph

theorem atState {p q : Program 4} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalHereditaryLambda.atState p)
      (OriginalHereditaryLambda.atState q) := by
  unfold OriginalHereditaryLambda.atState
  exact postcompose hp _

theorem childCheck {p q : Program 4} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalLambdaGuardLeaf.childCheck p)
      (OriginalLambdaGuardLeaf.childCheck q) := by
  unfold OriginalLambdaGuardLeaf.childCheck
  exact postcompose hp _

theorem advanceGuard {p q : Program 4} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalHereditaryLambda.advanceGuard p)
      (OriginalHereditaryLambda.advanceGuard q) := by
  unfold OriginalHereditaryLambda.advanceGuard
  exact conjunctionCongruence (equivalentRefl _)
    (conjunctionCongruence (equivalentRefl _) (childCheck hp))

theorem transition {p q : Program 4} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalHereditaryLambda.transition p)
      (OriginalHereditaryLambda.transition q) := by
  unfold OriginalHereditaryLambda.transition
  exact branchCongruence (equivalentRefl _) (equivalentRefl _)
    (branchCongruence (equivalentRefl _)
      (branchCongruence (normalizeCongruence (atState (advanceGuard hp)))
        (equivalentRefl _) (equivalentRefl _)) (equivalentRefl _))

theorem run {p q : Program 4} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalHereditaryLambda.run p)
      (OriginalHereditaryLambda.run q) := by
  unfold OriginalHereditaryLambda.run
  exact postcompose (repeatCongruence (transition hp)) _

theorem guard {p q : Program 4} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalHereditaryLambda.guard p)
      (OriginalHereditaryLambda.guard q) := by
  unfold OriginalHereditaryLambda.guard
  exact precompose _ (fun _ => run hp)

theorem refined {p q : Program 4} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalHereditaryLambda.refined p)
      (OriginalHereditaryLambda.refined q) := by
  unfold OriginalHereditaryLambda.refined
  exact conjunctionCongruence hp (guard hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.HereditaryCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.HereditaryCongruenceProof
