module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameStatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector HistoryRuleSuffix
/-- Literal encoded singleton [1], the ORIGINAL zero-term prefix. -/
def base : Program 0 := applyTwo HistoryCodec.cons (constant 0 1) (constant 0 0)
/-- Recursion input [counter,previous]: prepend ORIGINAL successor token2. -/
def step : Program 2 := applyTwo HistoryCodec.cons (constant 2 2) (.projection 1)
/-- One explicit unary AST, chosen before every runtime numeral/context. -/
def numeralCode : Program 1 := .recursion base step

def numeralCall {ctx : Nat} (tag : Nat) (value : Term ctx) : Term ctx := call tag (value ::ᵥ nil)
def termTask {ctx : Nat} (ptag : Nat) (binder : Term ctx) : Term ctx :=
 LiteralSyntaxStep.taskCall ptag 0 binder
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix
