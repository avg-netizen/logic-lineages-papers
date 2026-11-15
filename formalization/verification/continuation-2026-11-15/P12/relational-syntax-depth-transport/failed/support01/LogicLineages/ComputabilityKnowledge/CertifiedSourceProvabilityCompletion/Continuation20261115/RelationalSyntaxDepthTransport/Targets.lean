module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Original scanner success to empty stack is preserved by aligned task-kind
and nondecreasing bound relation. Inputs/raw codes are arbitrary. No step,
iterator simulation, expansion success, native calibration, or list-code image
is a premise. All requisite simulation and arithmetic must be proved internally. -/
def InternalClosedScanTransport : Prop := ∀ n (p : Program n)
 (stag lengthTag lookupTag ptag ctag atag leftTag rightTag : Nat),
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[lengthTag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[lookupTag]? = some ⟨2,HistoryLookup.lookup⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (tasks newTasks raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation lengthTag lookupTag leftTag rightTag tasks newTasks)
  (.imp (.equal (LiteralSyntaxScan.scanCall stag tasks raw) (.succ .zero))
   (.equal (LiteralSyntaxScan.scanCall stag newTasks raw) (.succ .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.Targets
