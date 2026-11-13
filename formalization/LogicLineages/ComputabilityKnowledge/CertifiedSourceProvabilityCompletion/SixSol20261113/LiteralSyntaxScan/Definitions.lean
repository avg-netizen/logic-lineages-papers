module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector HistoryRuleSuffix
/-- Literal iterator state: pair(remaining token-list code, Option task-stack code). -/
def remaining : Program 1 := HistoryDecoder.decoder false
def taskState : Program 1 := HistoryDecoder.decoder true
/-- Empty remaining input is an identity step, not a scanner failure. -/
def tick : Program 1 :=
 choose remaining (.projection 0)
  (applyTwo HistoryCodec.pair
   (applyOne HistoryLookup.tail remaining)
   (applyTwo LiteralSyntaxStep.stepCode taskState (applyOne HistoryLookup.head remaining)))
/-- Inputs [count,state]. Exactly count actual tick steps. -/
def iterator : Program 2 :=
 .recursion (.projection 0) (applyOne tick (.projection 1))
/-- Inputs [tasks,raw]. Initial stack is SOME tasks; fuel is actual raw length. -/
def initial : Program 2 := applyTwo HistoryCodec.pair (.projection 1)
 (applyOne .succ (.projection 0))
def finalState : Program 2 := applyTwo iterator
 (applyOne HistoryLengthOffset.lengthProgram (.projection 1)) initial
def scanCode : Program 2 := applyOne (HistoryDecoder.decoder true) finalState
def scanCall {ctx : Nat} (tag : Nat) (tasks raw : Term ctx) : Term ctx :=
 call tag (tasks ::ᵥ raw ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan
