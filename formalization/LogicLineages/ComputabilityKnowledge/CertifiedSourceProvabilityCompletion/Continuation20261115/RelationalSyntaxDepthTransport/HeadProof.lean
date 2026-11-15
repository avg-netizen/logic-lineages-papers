module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.RelationLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.HeadProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationLogicProof SubstitutionProof

theorem witnessHead {n ctx : Nat} (p : Program n) (q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oldHead newHead newTail : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (witness q l r (HistoryLookup.consCall ctag newHead newTail) .zero oldHead)
  (taskRelation l r oldHead newHead))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := witnessBody q l r (HistoryLookup.consCall ctag newHead newTail) .zero oldHead
 let Q := taskRelation l r oldHead newHead
 have hh : Hilbert.Local T (ctx+1) [P] P := .hypothesis List.mem_cons_self
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 obtain ⟨hz⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p q ctag hq hc (ctx+1)
  (liftTerm newHead) (liftTerm newTail)
 have hz' : Derivation T
  (.equal (HistoryLookup.lookupCall q (liftTerm .zero)
   (liftTerm (HistoryLookup.consCall ctag newHead newTail))) (.succ (liftTerm newHead))) := by
  simpa only [liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons,substitute] using hz
 have hsucc := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) (.base hz')
 have hv : Hilbert.Local T (ctx+1) [P] (.equal (.var 0) (liftTerm newHead)) :=
  .mp (.base (.arithmetic (.succInjective _ _))) hsucc
 have hout := Hilbert.Local.mp (.mp (.base (taskRight l r (liftTerm oldHead) (.var 0) (liftTerm newHead))) hv) hrel
 have hb : Derivation T (.imp P (GorbowPACore.weaken Q)) := by
  simpa only [Q,GorbowPACore.weaken,substTask,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 exact HBQuantifier.existentialElimination T P Q ⟨hb⟩

theorem consHeads {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oldHead oldTail newHead newTail : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation len q l r (HistoryLookup.consCall ctag oldHead oldTail) (HistoryLookup.consCall ctag newHead newTail))
  (taskRelation l r oldHead newHead))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := stackRelation len q l r (HistoryLookup.consCall ctag oldHead oldTail) (HistoryLookup.consCall ctag newHead newTail)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hi := Hilbert.Local.mp (.base (instanceRule len q l r _ _ .zero oldHead)) hh
 obtain ⟨hz⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p q ctag hq hc ctx oldHead oldTail
 have hw := Hilbert.Local.mp hi (.base hz)
 obtain ⟨he⟩ := witnessHead p q l r ctag hq hc oldHead newHead newTail
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base he) hw))⟩

theorem consTailLengths {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hl : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oldHead oldTail newHead newTail : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation len q l r (HistoryLookup.consCall ctag oldHead oldTail) (HistoryLookup.consCall ctag newHead newTail))
  (.equal (HistoryLengthOffset.lengthCall len oldTail) (HistoryLengthOffset.lengthCall len newTail)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := stackRelation len q l r (HistoryLookup.consCall ctag oldHead oldTail) (HistoryLookup.consCall ctag newHead newTail)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 obtain ⟨ho⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p len ctag hl hc ctx oldHead oldTail
 obtain ⟨hn⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p len ctag hl hc ctx newHead newTail
 have hs := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ ho)) (localTrans _ _ _ he (.base hn))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base (.arithmetic (.succInjective _ _))) hs))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.HeadProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.HeadProof
