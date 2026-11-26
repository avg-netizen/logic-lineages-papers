module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TailProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConsEntriesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationLogicProof SubstitutionProof TailProof

noncomputable def taskLeft {T : Sentence → Prop} {ctx : Nat} l r (a b t : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (taskRelation l r a t) (taskRelation l r b t))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (taskRelation l r (.var 0) (liftTerm t)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substTask,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

/-- Rebuild the actual successor lookup witness after pushing a task. -/
theorem witnessCons {n ctx : Nat} (p : Program n) (q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (head tail index task : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (witness q l r tail index task)
  (witness q l r (HistoryLookup.consCall ctag head tail) (.succ index) task))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := witnessBody q l r tail index task
 let Q := witness q l r (HistoryLookup.consCall ctag head tail) (.succ index) task
 have hh : Hilbert.Local T (ctx+1) [P] P := .hypothesis List.mem_cons_self
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 obtain ⟨hs⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p q ctag hq hc (ctx+1)
  (liftTerm index) (liftTerm head) (liftTerm tail)
 have hhead := localTrans _ _ _ (.base hs) he
 have hboth := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hhead) hrel
 have hout := Hilbert.Local.mp (.base (witnessIntro q l r
  (HistoryLookup.consCall ctag (liftTerm head) (liftTerm tail)) (.succ (liftTerm index)) (liftTerm task) (.var 0))) hboth
 have hb : Derivation T (.imp P (GorbowPACore.weaken Q)) := by
  simpa only [Q,GorbowPACore.weaken,substWitness,liftTerm,renameTerm,
   HistoryLookup.DropEquationsProof.substCons,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 exact HBQuantifier.existentialElimination T P Q ⟨hb⟩

/-- The zero entry is supplied by the actual related heads, not a lookup axiom. -/
theorem zeroEntry {n ctx : Nat} (p : Program n) (q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oh ot nh nt task : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (taskRelation l r oh nh)
  (entryBody q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt) .zero task))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := taskRelation l r oh nh
 let E := Formula.equal (HistoryLookup.lookupCall q .zero (HistoryLookup.consCall ctag oh ot)) (.succ task)
 have hh : Hilbert.Local T ctx [E,H] H := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,H] E := .hypothesis List.mem_cons_self
 obtain ⟨ho⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p q ctag hq hc ctx oh ot
 obtain ⟨hn⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p q ctag hq hc ctx nh nt
 have hs := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ ho)) he
 have ht : Hilbert.Local T ctx [E,H] (.equal oh task) := .mp (.base (.arithmetic (.succInjective _ _))) hs
 have hr := Hilbert.Local.mp (.mp (.base (taskLeft l r oh task nh)) ht) hh
 have hb := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.base hn)) hr
 have hw := Hilbert.Local.mp (.base (witnessIntro q l r (HistoryLookup.consCall ctag nh nt) .zero task nh)) hb
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hw))⟩

/-- Successor entries are supplied by related tails and both original cons lookup equations. -/
theorem successorEntry {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oh ot nh nt index task : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation len q l r ot nt)
  (entryBody q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt) (.succ index) task))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := stackRelation len q l r ot nt
 let E := Formula.equal (HistoryLookup.lookupCall q (.succ index) (HistoryLookup.consCall ctag oh ot)) (.succ task)
 have hh : Hilbert.Local T ctx [E,H] H := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,H] E := .hypothesis List.mem_cons_self
 obtain ⟨hs⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p q ctag hq hc ctx index oh ot
 have ht := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hs)) he
 have hi := Hilbert.Local.mp (.base (instanceRule len q l r ot nt index task)) hh
 have hw := Hilbert.Local.mp hi ht
 obtain ⟨hcw⟩ := witnessCons p q l r ctag hq hc nh nt index task
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.base hcw) hw)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConsEntriesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConsEntriesProof
