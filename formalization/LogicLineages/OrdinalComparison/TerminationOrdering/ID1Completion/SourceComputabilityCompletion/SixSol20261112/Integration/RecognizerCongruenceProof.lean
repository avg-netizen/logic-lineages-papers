module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.HereditaryCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.RecognizerCongruenceProof
open InternalControlGraph
open GraphCongruenceProof OperatorCongruenceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] ProgramGraphEquivalent programGraph

theorem sourceAt {p q : Program 2} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalTransparentVariableStep.sourceAt p)
      (OriginalTransparentVariableStep.sourceAt q) := by
  unfold OriginalTransparentVariableStep.sourceAt
  exact postcompose hp _

theorem lambdaGuard {p q : Program 2} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalTransparentLambdaStep.hopGuard p)
      (OriginalTransparentLambdaStep.hopGuard q) := by
  unfold OriginalTransparentLambdaStep.hopGuard
  exact conjunctionCongruence (sourceAt hp) (equivalentRefl _)

theorem applicationGuard {p q : Program 2} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (OriginalTransparentApplicationFunctionDefinitions.hopGuard p)
      (OriginalTransparentApplicationFunctionDefinitions.hopGuard q) := by
  unfold OriginalTransparentApplicationFunctionDefinitions.hopGuard
  exact conjunctionCongruence (sourceAt hp) (equivalentRefl _)

theorem lambdaHop {p q : Program 2} {leaf other : Program 4}
    (hp : ProgramGraphEquivalent p q) (hl : ProgramGraphEquivalent leaf other) :
    ProgramGraphEquivalent (OriginalMixedDirectBottomTrace.lambdaHop p leaf)
      (OriginalMixedDirectBottomTrace.lambdaHop q other) := by
  unfold OriginalMixedDirectBottomTrace.lambdaHop
  exact conjunctionCongruence (lambdaGuard hp) hl

theorem applicationHop {p q : Program 2} {leaf other : Program 4}
    (hp : ProgramGraphEquivalent p q) (hl : ProgramGraphEquivalent leaf other) :
    ProgramGraphEquivalent (OriginalMixedDirectBottomTrace.applicationHop p leaf)
      (OriginalMixedDirectBottomTrace.applicationHop q other) := by
  unfold OriginalMixedDirectBottomTrace.applicationHop
  exact conjunctionCongruence (applicationGuard hp) hl

theorem transition {p q : Program 2} {leaf other : Program 4}
    (hp : ProgramGraphEquivalent p q) (hl : ProgramGraphEquivalent leaf other) :
    ProgramGraphEquivalent (OriginalMixedDirectBottomTrace.transition p leaf)
      (OriginalMixedDirectBottomTrace.transition q other) := by
  unfold OriginalMixedDirectBottomTrace.transition
  exact branchCongruence (equivalentRefl _) (equivalentRefl _)
    (branchCongruence
      (normalizeCongruence (HereditaryCongruenceProof.atState (lambdaHop hp hl)))
      (branchCongruence
        (normalizeCongruence (HereditaryCongruenceProof.atState (applicationHop hp hl)))
        (equivalentRefl _) (equivalentRefl _)) (equivalentRefl _))

theorem terminal {p q : Program 2} {leaf other : Program 4}
    (hp : ProgramGraphEquivalent p q) (hl : ProgramGraphEquivalent leaf other) :
    ProgramGraphEquivalent (OriginalMixedDirectBottomTrace.terminal p leaf)
      (OriginalMixedDirectBottomTrace.terminal q other) := by
  unfold OriginalMixedDirectBottomTrace.terminal OriginalLambdaDirectBottomTrace.terminal
  exact conjunctionCongruence (sourceAt hp) (conjunctionCongruence hl (equivalentRefl _))

theorem finish {p q : Program 2} {leaf other : Program 4}
    (hp : ProgramGraphEquivalent p q) (hl : ProgramGraphEquivalent leaf other) :
    ProgramGraphEquivalent (OriginalMixedDirectBottomTrace.finish p leaf)
      (OriginalMixedDirectBottomTrace.finish q other) := by
  unfold OriginalMixedDirectBottomTrace.finish
  exact branchCongruence (equivalentRefl _) (equivalentRefl _)
    (HereditaryCongruenceProof.atState (terminal hp hl))

theorem run {p q : Program 2} {leaf other : Program 4}
    (hp : ProgramGraphEquivalent p q) (hl : ProgramGraphEquivalent leaf other) :
    ProgramGraphEquivalent (OriginalMixedDirectBottomTrace.run p leaf)
      (OriginalMixedDirectBottomTrace.run q other) := by
  unfold OriginalMixedDirectBottomTrace.run
  exact postcompose (repeatCongruence (transition hp hl)) _

theorem recognizes {p q : Program 2} {leaf other : Program 4}
    (hp : ProgramGraphEquivalent p q) (hl : ProgramGraphEquivalent leaf other) :
    ProgramGraphEquivalent (OriginalMixedDirectBottomTrace.recognizes p leaf)
      (OriginalMixedDirectBottomTrace.recognizes q other) := by
  unfold OriginalMixedDirectBottomTrace.recognizes
  exact compositionCongruence (finish hp hl) (fun _ => run hp hl)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.RecognizerCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.RecognizerCongruenceProof
