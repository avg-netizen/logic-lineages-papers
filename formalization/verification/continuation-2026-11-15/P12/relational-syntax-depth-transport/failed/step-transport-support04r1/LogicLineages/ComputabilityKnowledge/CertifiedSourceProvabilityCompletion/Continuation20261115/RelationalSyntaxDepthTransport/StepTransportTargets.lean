module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.RelatedConsStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 SixSol20261112.Fuel
/-- Actual new successful step and aligned output stacks, at one original registry. -/
def witnessBody {ctx : Nat} (stag len q l r : Nat)
 (newTasks tok oldResult newResult : Term ctx) : Formula ctx :=
 .conj (.equal (LiteralSyntaxStep.stepCall stag (.succ newTasks) tok) (.succ newResult))
  (stackRelation len q l r oldResult newResult)
/-- The sole bound variable is the new raw result stack. All external runtime
terms are lifted once; success remains the original option-successor convention. -/
def witnesses {ctx : Nat} (stag len q l r : Nat)
 (newTasks tok oldResult : Term ctx) : Formula ctx :=
 .ex (witnessBody stag len q l r (liftTerm newTasks) (liftTerm tok)
  (liftTerm oldResult) (.var 0))
/-- One original successful step transports across the original pointwise stack
relation, for arbitrary runtime codes. No expansion success, constructor case,
new-stack cons representation, difference installation, or transfer is assumed. -/
def InternalSuccessfulStepTransport : Prop := ∀ n (p : Program n)
 (stag etag ptag ctag atag len q l r : Nat),
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩ →
 (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (oldTasks newTasks tok oldResult : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (stackRelation len q l r oldTasks newTasks)
   (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ oldTasks) tok) (.succ oldResult))
    (witnesses stag len q l r newTasks tok oldResult))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportTargets
