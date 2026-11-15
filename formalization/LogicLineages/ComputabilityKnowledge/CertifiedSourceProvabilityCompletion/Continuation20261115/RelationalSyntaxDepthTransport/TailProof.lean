module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.HeadProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.TailProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationLogicProof SubstitutionProof

theorem witnessAt {ctx : Nat} q l r (b i t w : Term ctx) :
 GorbowStandardInstances.instantiate (witnessBody q l r b i t) w =
 .conj (.equal (HistoryLookup.lookupCall q i b) (.succ w)) (taskRelation l r t w) := by
 simp only [GorbowStandardInstances.instantiate,witnessBody,substituteFormula,HistoryLookup.lookupCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substTask,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def witnessIntro {T : Sentence → Prop} {ctx : Nat} q l r (b i t w : Term ctx) :
 Derivation T (.imp (.conj (.equal (HistoryLookup.lookupCall q i b) (.succ w)) (taskRelation l r t w))
  (witness q l r b i t)) := by
 have h := HistoryOrder.SupportProof.existsIntroRule (T := T) (witnessBody q l r b i t) w
 rwa [witnessAt] at h

theorem witnessTail {n ctx : Nat} (p : Program n) (q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (head tail index task : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (witness q l r (HistoryLookup.consCall ctag head tail) (.succ index) task)
  (witness q l r tail index task))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := witnessBody q l r (HistoryLookup.consCall ctag head tail) (.succ index) task
 let Q := witness q l r tail index task
 have hh : Hilbert.Local T (ctx+1) [P] P := .hypothesis List.mem_cons_self
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 obtain ⟨hs⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p q ctag hq hc (ctx+1)
  (liftTerm index) (liftTerm head) (liftTerm tail)
 have hs' : Derivation T
  (.equal (HistoryLookup.lookupCall q (liftTerm (.succ index))
   (liftTerm (HistoryLookup.consCall ctag head tail)))
   (HistoryLookup.lookupCall q (liftTerm index) (liftTerm tail))) := by
  simpa only [liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons,substitute] using hs
 have htail := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hs')) he
 have hboth := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) htail) hrel
 have hout := Hilbert.Local.mp (.base (witnessIntro q l r (liftTerm tail) (liftTerm index) (liftTerm task) (.var 0))) hboth
 have hb : Derivation T (.imp P (GorbowPACore.weaken Q)) := by
  simpa only [Q,GorbowPACore.weaken,substWitness,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 exact HBQuantifier.existentialElimination T P Q ⟨hb⟩

theorem tailEntry {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (oh ot nh nt i t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation len q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt))
  (entryBody q l r ot nt i t))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := stackRelation len q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt)
 let E := Formula.equal (HistoryLookup.lookupCall q i ot) (.succ t)
 have hp : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 obtain ⟨hs⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p q ctag hq hc ctx i oh ot
 have hhead := localTrans _ _ _ (.base hs) he
 have hi := Hilbert.Local.mp (.base (instanceRule len q l r _ _ (.succ i) t)) hp
 obtain ⟨ht⟩ := witnessTail p q l r ctag hq hc nh nt i t
 have hout := Hilbert.Local.mp (.base ht) (.mp hi hhead)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

theorem tailIndex {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (oh ot nh nt i : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation len q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt))
  (entryRelation q l r ot nt i))) := by
 let P := stackRelation len q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt)
 obtain ⟨h⟩ := tailEntry p len q l r ctag hq hc (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt) (liftTerm i) (.var (0 : Fin (ctx+1)))
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken P) (entryBody q l r (liftTerm ot) (liftTerm nt) (liftTerm i) (.var 0))) := by
  simpa only [P,GorbowPACore.weaken,substStack,HistoryLookup.consCall,Logic.substCall,
   List.Vector.map_cons,List.Vector.map_nil,liftTerm,renameTerm] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder P _ h'⟩

theorem consTails {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hl : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (oh ot nh nt : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation len q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt))
  (stackRelation len q l r ot nt))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := stackRelation len q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt)
 obtain ⟨h⟩ := tailIndex p len q l r ctag hq hc (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt) (.var (0 : Fin (ctx+1)))
 have h' : Derivation T (.imp (GorbowPACore.weaken P)
  (entryRelation q l r (liftTerm ot) (liftTerm nt) (.var 0))) := by
  simpa only [P,GorbowPACore.weaken,substStack,HistoryLookup.consCall,Logic.substCall,
   List.Vector.map_cons,List.Vector.map_nil,liftTerm,renameTerm] using h
 have hall := HistoryIteratorSuffix.RelationProof.universalUnder P _ h'
 obtain ⟨hlen⟩ := HeadProof.consTailLengths p len q l r ctag hl hc oh ot nh nt
 have hp : Hilbert.Local T ctx [P] P := .hypothesis List.mem_cons_self
 have both := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.mp (.base hlen) hp)) (.mp (.base hall) hp)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge both)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.TailProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.TailProof
