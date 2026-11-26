module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConsEntriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationLogicProof SubstitutionProof

def property {ctx : Nat} (len q l r ctag : Nat) (oh ot nh nt i : Term ctx) : Formula ctx :=
 .imp (.conj (taskRelation l r oh nh) (stackRelation len q l r ot nt))
  (entryRelation q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt) i)
theorem substProperty {m n : Nat} (s : Fin m → Term n) len q l r ctag (oh ot nh nt i : Term m) :
 substituteFormula s (property len q l r ctag oh ot nh nt i) =
 property len q l r ctag (substitute s oh) (substitute s ot) (substitute s nh) (substitute s nt) (substitute s i) := by
 simp only [property,substituteFormula,substTask,substStack,substEntry,HistoryLookup.DropEquationsProof.substCons]

theorem zeroIndex {n ctx : Nat} (p : Program n) (q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oh ot nh nt : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (taskRelation l r oh nh)
  (entryRelation q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt) .zero))) := by
 let P := taskRelation l r oh nh
 obtain ⟨h⟩ := ConsEntriesProof.zeroEntry p q l r ctag hq hc
  (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt) (.var (0 : Fin (ctx+1)))
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken P)
   (entryBody q l r (liftTerm (HistoryLookup.consCall ctag oh ot))
    (liftTerm (HistoryLookup.consCall ctag nh nt)) (liftTerm .zero) (.var 0))) := by
  simpa only [P,GorbowPACore.weaken,substTask,liftTerm,renameTerm,
   HistoryLookup.DropEquationsProof.substCons,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder P _ h'⟩

theorem successorIndex {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oh ot nh nt i : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation len q l r ot nt)
  (entryRelation q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt) (.succ i)))) := by
 let P := stackRelation len q l r ot nt
 obtain ⟨h⟩ := ConsEntriesProof.successorEntry p len q l r ctag hq hc
  (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt) (liftTerm i) (.var (0 : Fin (ctx+1)))
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken P)
   (entryBody q l r (liftTerm (HistoryLookup.consCall ctag oh ot))
    (liftTerm (HistoryLookup.consCall ctag nh nt)) (liftTerm (.succ i)) (.var 0))) := by
  simpa only [P,GorbowPACore.weaken,substStack,liftTerm,renameTerm,
   HistoryLookup.DropEquationsProof.substCons,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder P _ h'⟩

/-- Original PA induction covers every raw lookup index, including out-of-range entries. -/
theorem atIndex {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oh ot nh nt i : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (property len q l r ctag oh ot nh nt i)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := property len q l r ctag (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt) (.var (0 : Fin (ctx+1)))
 obtain ⟨hz⟩ := zeroIndex p q l r ctag hq hc oh ot nh nt
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simp only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
  exact Hilbert.compose hz (.logical (.andLeft _ _))
 obtain ⟨hn⟩ := successorIndex p len q l r ctag hq hc
  (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt) (.var (0 : Fin (ctx+1)))
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simp only [phi,GorbowStandardInduction.successorInstance,substProperty,substitute,successorLift,Fin.cases_zero]
  exact Hilbert.lift _ (Hilbert.compose hn (.logical (.andRight _ _)))
 have h := atTerm phi i (HistoryCodec.ArithmeticSupport.induction phi hb hs)
 simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using (show Nonempty _ from ⟨h⟩)

/-- Assemble the complete relation on genuine encoded cons stacks from related
heads and tails, including actual length and universally quantified lookup duties. -/
theorem consRelated {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hl : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (oh ot nh nt : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.conj (taskRelation l r oh nh) (stackRelation len q l r ot nt))
  (stackRelation len q l r (HistoryLookup.consCall ctag oh ot) (HistoryLookup.consCall ctag nh nt)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := Formula.conj (taskRelation l r oh nh) (stackRelation len q l r ot nt)
 obtain ⟨hi⟩ := atIndex p len q l r ctag hq hc
  (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt) (.var (0 : Fin (ctx+1)))
 have hi' : Derivation T (.imp (GorbowPACore.weaken P)
  (entryRelation q l r (liftTerm (HistoryLookup.consCall ctag oh ot))
   (liftTerm (HistoryLookup.consCall ctag nh nt)) (.var 0))) := by
  simpa only [property,P,GorbowPACore.weaken,substituteFormula,substTask,substStack,
   liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons] using hi
 have hall := HistoryIteratorSuffix.RelationProof.universalUnder P _ hi'
 have hp : Hilbert.Local T ctx [P] P := .hypothesis List.mem_cons_self
 have ht := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hp
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ht
 have hs := localUnary (.succ (.var 0)) _ _ he
 obtain ⟨ho⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p len ctag hl hc ctx oh ot
 obtain ⟨hn⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p len ctag hl hc ctx nh nt
 have hlen := localTrans _ _ _ (.base ho) (localTrans _ _ _ hs (.base (Support.equalitySymmetry _ _ hn)))
 have hout := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hlen) (.mp (.base hall) hp)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConsProof
