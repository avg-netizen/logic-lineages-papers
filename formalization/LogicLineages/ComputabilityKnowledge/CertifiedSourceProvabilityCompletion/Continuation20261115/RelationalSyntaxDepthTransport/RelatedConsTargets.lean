module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.RelatedConsTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261113 SixSol20261112.Fuel
/-- Exact recovered new cons witnesses and both original task/tail relations. -/
def witnessBody {ctx : Nat} (len q l r ctag : Nat)
 (oldHead oldTail newTasks newHead newTail : Term ctx) : Formula ctx :=
 .conj (.equal newTasks (HistoryLookup.consCall ctag newHead newTail))
  (.conj (taskRelation l r oldHead newHead) (stackRelation len q l r oldTail newTail))
/-- Quantifier order newHead,newTail; original bound indices1,0 and external
runtime terms lifted twice. -/
def witnesses {ctx : Nat} (len q l r ctag : Nat) (oldHead oldTail newTasks : Term ctx) : Formula ctx :=
 .ex (.ex (witnessBody len q l r ctag (liftTerm (liftTerm oldHead))
  (liftTerm (liftTerm oldTail)) (liftTerm (liftTerm newTasks)) (.var 1) (.var 0)))
/-- A raw stack related to an actual cons is internally another cons, with
related head and tail. New-stack positivity or encoded-list image is NOT a premise. -/
def InternalRelatedCons : Prop := ∀ n (p : Program n) (len q l r ctag : Nat),
 (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (oldHead oldTail newTasks : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (stackRelation len q l r (HistoryLookup.consCall ctag oldHead oldTail) newTasks)
   (witnesses len q l r ctag oldHead oldTail newTasks)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.RelatedConsTargets
