module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowTermShiftCodeProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
/-- Inputs [original Option-task-stack code, token, replacement raw-list code]. -/
def stackCode : Program 3 := applyOne HistoryCodec.predecessor (.projection 0)
def taskCode : Program 3 := applyOne HistoryLookup.head stackCode
def kindCode : Program 3 := applyOne (HistoryDecoder.decoder false) taskCode
def boundCode : Program 3 := applyOne (HistoryDecoder.decoder true) taskCode
/-- Original emit n=1 uses truncated context-1, including malformed bound0. -/
def depthCode : Program 3 := applyOne HistoryCodec.predecessor boundCode
def singletonCode : Program 3 := applyTwo HistoryCodec.cons (.projection 1) (constant 3 0)
def variableCode : Program 3 := applyTwo HistoryCodec.cons (constant 3 0) singletonCode
/-- difference(token,depth)=depth-token. The equal branch returns the actual
runtime replacement code; an out-of-range dictionary lookup emits []. -/
def indexCode : Program 3 :=
 choose (applyTwo HistoryCodec.difference (.projection 1) depthCode)
  (choose (applyTwo equalCode (.projection 1) depthCode) (constant 3 0) (.projection 2))
  variableCode
def nonIndexCode : Program 3 :=
 choose (applyTwo equalCode kindCode (constant 3 0)) singletonCode
  (choose (.projection 1) (constant 3 0) singletonCode)
def activeCode : Program 3 :=
 choose (applyTwo equalCode kindCode (constant 3 2)) nonIndexCode indexCode
/-- NONE and SOME[] preserve original emit's [token] fallback. All other
natural codes retain original decoding; no additional malformed-input guard. -/
def emitCode : Program 3 :=
 choose (.projection 0) singletonCode (choose stackCode singletonCode activeCode)
def emitCall {ctx : Nat} (tag : Nat) (state token raw : Term ctx) : Term ctx :=
 call tag (state ::ᵥ token ::ᵥ raw ::ᵥ nil)
def stateValue {ctx : Nat} (ptag ctag : Nat) (kind bound rest : Term ctx) : Term ctx :=
 .succ (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag kind bound) rest)
def singletonValue {ctx : Nat} (ctag : Nat) (token : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag token .zero
def variableValue {ctx : Nat} (ctag : Nat) (token : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero (singletonValue ctag token)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit
