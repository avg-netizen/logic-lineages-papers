module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.SyntaxDepthTransport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix
/-- Shift the bound in the ORIGINAL (kind,bound) task, preserving every kind,
including invalid kinds. Inputs [task,delta]. -/
def shiftedTask : Program 2 :=
 applyTwo HistoryCodec.pair
  (applyOne (HistoryDecoder.decoder false) (.projection 0))
  (applyTwo HistoryCodec.add (applyOne (HistoryDecoder.decoder true) (.projection 0)) (.projection 1))
/-- Finite course-of-values table exactly as original append, but with zero
base and shifted head. No unchecked lookup success is assumed. -/
def tableBase : Program 1 := applyTwo HistoryCodec.cons (constant 1 0) (constant 1 0)
def tableValue : Program 3 :=
 applyTwo HistoryCodec.cons
  (applyTwo shiftedTask HistoryAppend.inputHead (.projection 2))
  HistoryAppend.recursiveResult
def tableStep : Program 3 := applyTwo HistoryCodec.cons tableValue (.projection 1)
def table : Program 2 := .recursion tableBase tableStep
/-- Inputs [encoded task stack,delta], output original list coding. -/
def stackShift : Program 2 := applyOne HistoryLookup.head table
def shiftCall {ctx : Nat} (tag : Nat) (stack delta : Term ctx) : Term ctx :=
 call tag (List.Vector.cons stack (List.Vector.cons delta List.Vector.nil))
def shiftedTaskValue {ctx : Nat} (ptag ltag rtag : Nat) (task delta : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (call ltag (List.Vector.cons task List.Vector.nil))
  (.add (call rtag (List.Vector.cons task List.Vector.nil)) delta)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.SyntaxDepthTransport
