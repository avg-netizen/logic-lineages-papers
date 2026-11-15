module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261113 SixSol20261112.Fuel
/-- Original iterator state projection after the actual raw length. The sole
existential variable is the new successful final task-stack, not a run oracle. -/
def witnessBody {ctx : Nat} (itag len ptag q l r : Nat)
 (raw newTasks oldResult newResult : Term ctx) : Formula ctx :=
 .conj (.equal (LiteralSyntaxScan.StateRecursionProof.scanState itag len ptag r raw (.succ newTasks))
   (.succ newResult))
  (stackRelation len q l r oldResult newResult)
def witnesses {ctx : Nat} (itag len ptag q l r : Nat)
 (raw newTasks oldResult : Term ctx) : Formula ctx :=
 .ex (witnessBody itag len ptag q l r (liftTerm raw) (liftTerm newTasks) (liftTerm oldResult) (.var 0))
/-- Success transport for the ACTUAL iterator/length/pair/right projection at
all raw codes. No tick/iteration simulation, prefix image, exhaustion, or
induction hypothesis is an external premise. All changing stack coordinates
must remain internally generalized during the raw-bound induction. -/
def InternalScanStateTransport : Prop := ∀ n (p : Program n)
 (itag stag etag ptag ctag atag len q l r : Nat),
 (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩ →
 (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (raw oldTasks newTasks oldResult : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (stackRelation len q l r oldTasks newTasks)
   (.imp (.equal (LiteralSyntaxScan.StateRecursionProof.scanState itag len ptag r raw (.succ oldTasks))
     (.succ oldResult))
    (witnesses itag len ptag q l r raw newTasks oldResult))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportTargets
