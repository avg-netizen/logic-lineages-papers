module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
/-- Inputs [encoded OutputState, token, closed replacement code]. -/
def syntaxState : Program 3 := applyOne (HistoryDecoder.decoder false) (.projection 0)
def output : Program 3 := applyOne (HistoryDecoder.decoder true) (.projection 0)
def emitted : Program 3 := .composition UniformClosedSubstitutionEmit.emitCode
 (fun i => (syntaxState ::ᵥ (.projection 1) ::ᵥ (.projection 2) ::ᵥ nil).get i)
def subStepCode : Program 3 := applyTwo HistoryCodec.pair
 (applyTwo LiteralSyntaxStep.stepCode syntaxState (.projection 1))
 (applyTwo HistoryAppend.append output emitted)
/-- Tick inputs [pair(remaining,OutputState), replacement]. No validity guard:
original NONE/empty/malformed syntax states still emit their original chunks. -/
def remaining : Program 2 := applyOne (HistoryDecoder.decoder false) (.projection 0)
def accumulator : Program 2 := applyOne (HistoryDecoder.decoder true) (.projection 0)
def advanced : Program 2 := .composition subStepCode
 (fun i => (accumulator ::ᵥ applyOne HistoryLookup.head remaining ::ᵥ (.projection 1) ::ᵥ nil).get i)
def tick : Program 2 := choose remaining (.projection 0)
 (applyTwo HistoryCodec.pair (applyOne HistoryLookup.tail remaining) advanced)
/-- Inputs [token count, initial packed state, replacement]. Count is raw.length,
not raw's encoded natural. Extra ticks on empty remaining input are identities. -/
def iterator : Program 3 := .recursion (.projection 0)
 (applyTwo tick (.projection 1) (.projection 3))
def subStepCall {ctx : Nat} (tag : Nat) (state token raw : Term ctx) : Term ctx :=
 call tag (state ::ᵥ token ::ᵥ raw ::ᵥ nil)
def iterateCall {ctx : Nat} (tag : Nat) (count state raw : Term ctx) : Term ctx :=
 call tag (count ::ᵥ state ::ᵥ raw ::ᵥ nil)
def tokenTerms {ctx : Nat} (ctag : Nat) : List (Term ctx) → Term ctx
 | [] => .zero
 | t :: ts => HistoryLookup.consCall ctag t (tokenTerms ctag ts)
/-- Explicit original syntax-state/output recurrence on finite runtime terms. -/
def foldTerms {ctx : Nat} (stag etag atag : Nat) (raw : Term ctx) :
 List (Term ctx) → Term ctx → Term ctx → Term ctx × Term ctx
 | [], state, out => (state,out)
 | token :: tokens, state, out => foldTerms stag etag atag raw tokens
   (LiteralSyntaxStep.stepCall stag state token)
   (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold
