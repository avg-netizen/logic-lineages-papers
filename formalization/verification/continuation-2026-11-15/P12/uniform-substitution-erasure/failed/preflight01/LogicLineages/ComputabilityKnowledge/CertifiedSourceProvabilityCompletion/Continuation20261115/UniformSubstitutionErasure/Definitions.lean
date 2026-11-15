module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
/-- Erase only accumulated output: pair(remaining,pair(syntax,out)) becomes
pair(remaining,syntax). This is a total fixed AST on arbitrary raw naturals. -/
def syntaxProjection : Program 1 := applyOne (HistoryDecoder.decoder false) (HistoryDecoder.decoder true)
def eraseCode : Program 1 := applyTwo HistoryCodec.pair (HistoryDecoder.decoder false) syntaxProjection
def eraseCall {ctx : Nat} (tag : Nat) (state : Term ctx) : Term ctx := call tag (state ::ᵥ nil)
def newTickCall {ctx : Nat} (tag : Nat) (state raw : Term ctx) : Term ctx := call tag (state ::ᵥ raw ::ᵥ nil)
def oldTickCall {ctx : Nat} (tag : Nat) (state : Term ctx) : Term ctx := call tag (state ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure
