module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
/-- Inputs [prefix,OutputState]. Preserve original syntax state, append prefix to
original accumulated output. All codes arbitrary; no validity guard. -/
def outputFrame : Program 2 := applyTwo HistoryCodec.pair
 (applyOne (HistoryDecoder.decoder false) (.projection 1))
 (applyTwo HistoryAppend.append (.projection 0) (applyOne (HistoryDecoder.decoder true) (.projection 1)))
/-- Inputs [prefix,packed state]. Preserve remaining tokens and syntax, modify
only accumulated output using the literal append program. -/
def packedFrame : Program 2 := applyTwo HistoryCodec.pair
 (applyOne (HistoryDecoder.decoder false) (.projection 1))
 (applyTwo outputFrame (.projection 0) (applyOne (HistoryDecoder.decoder true) (.projection 1)))
def frameCall {ctx : Nat} (tag : Nat) (prefixCode state : Term ctx) : Term ctx :=
 call tag (prefixCode ::ᵥ state ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame
