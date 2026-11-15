module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.SyntaxDepthTransport.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.SyntaxDepthTransport.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
/-- Original list/task coding; arbitrary kinds and bounds, not just valid stacks. -/
def NativeStackShift : Prop := ∀ (tasks : List (Nat × Nat)) (delta : Nat),
 evaluate stackShift (Encodable.encode tasks ::ᵥ delta ::ᵥ nil) =
 Encodable.encode (tasks.map (fun t => (t.1,t.2+delta)))
def InternalNil : Prop := ∀ n (p : Program n) mtag,
 (nodes p)[mtag]? = some ⟨2,stackShift⟩ → ∀ ctx (delta : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (shiftCall mtag .zero delta) .zero))
/-- Actual course-of-values stack map cons equation, no table-coverage premise. -/
def InternalCons : Prop := ∀ n (p : Program n) (mtag ptag ctag ltag rtag : Nat),
 (nodes p)[mtag]? = some ⟨2,stackShift⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (task rest delta : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (shiftCall mtag (HistoryLookup.consCall ctag task rest) delta)
  (HistoryLookup.consCall ctag (shiftedTaskValue ptag ltag rtag task delta) (shiftCall mtag rest delta))))
/-- Genuine original scanner success transport, including arbitrary invalid raw
codes/stacks. Only actual old scan success is assumed. It must be proved by
internal step/tick/iteration simulation, not native calibration. -/
def InternalScanTransport : Prop := ∀ n (p : Program n) (stag mtag ptag ctag atag ltag rtag : Nat),
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[mtag]? = some ⟨2,stackShift⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (tasks raw out delta : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralSyntaxScan.scanCall stag tasks raw) (.succ out))
  (.equal (LiteralSyntaxScan.scanCall stag (shiftCall mtag tasks delta) raw)
   (.succ (shiftCall mtag out delta)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.SyntaxDepthTransport.Targets
