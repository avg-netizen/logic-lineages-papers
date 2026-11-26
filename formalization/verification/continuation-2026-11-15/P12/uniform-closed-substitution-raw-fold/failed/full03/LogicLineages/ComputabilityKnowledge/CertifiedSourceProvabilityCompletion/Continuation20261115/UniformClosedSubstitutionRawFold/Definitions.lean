module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
/-- Inputs [arbitrary encoded token list, initial OutputState, replacement]. -/
def initial : Program 3 := applyTwo HistoryCodec.pair (.projection 0) (.projection 1)
def finalPacked : Program 3 := .composition UniformClosedSubstitutionFold.iterator
 (fun i => (applyOne HistoryLengthOffset.lengthProgram (.projection 0) ::ᵥ initial ::ᵥ (.projection 2) ::ᵥ nil).get i)
def foldCode : Program 3 := applyOne (HistoryDecoder.decoder true) finalPacked
def foldCall {ctx : Nat} (tag : Nat) (tokens state raw : Term ctx) : Term ctx :=
 call tag (tokens ::ᵥ state ::ᵥ raw ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold
