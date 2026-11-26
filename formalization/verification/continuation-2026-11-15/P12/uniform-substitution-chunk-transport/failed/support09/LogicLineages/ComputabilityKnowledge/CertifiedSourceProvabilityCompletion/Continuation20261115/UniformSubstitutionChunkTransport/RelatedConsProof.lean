module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelatedConsTargets RelatedConsWitnessProof

theorem empty {n ctx : Nat} (p : Program n) (len q l r c : Nat)
 (hl : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (oh ot : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property len q l r c oh ot .zero)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := stackRelation len q l r (HistoryLookup.consCall c oh ot) (.zero : Term ctx)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 obtain ⟨hcons⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p len c hl hc ctx oh ot
 obtain ⟨hnil⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p len hl ctx
 have hbad := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hcons)) (localTrans _ _ _ he (.base hnil))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (Hilbert.Local.explosion (witnesses len q l r c oh ot .zero) hbad
   (.base (.arithmetic (.succNotZero (HistoryLengthOffset.lengthCall len ot))))))⟩

theorem cons {n ctx : Nat} (p : Program n) (len q l r c : Nat)
 (hl : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (oh ot nh nt : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property len q l r c oh ot (HistoryLookup.consCall c nh nt))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := stackRelation len q l r (HistoryLookup.consCall c oh ot) (HistoryLookup.consCall c nh nt)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hhead⟩ := HeadProof.consHeads p len q l r c hq hc oh ot nh nt
 obtain ⟨htail⟩ := TailProof.consTails p len q l r c hl hq hc oh ot nh nt
 have hrel := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.mp (.base hhead) hh)) (.mp (.base htail) hh)
 have hb := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _)))
  (.base (.logical (.reflexive (HistoryLookup.consCall c nh nt))))) hrel
 have hw := Hilbert.Local.mp (.base (witnessIntro len q l r c oh ot (HistoryLookup.consCall c nh nt) nh nt)) hb
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hw)⟩

/-- Positive NEW raw codes obtain their witnesses from original internal pair
surjectivity; the old stack is fixed and no cons image is assumed for the new. -/
theorem positive {n ctx : Nat} (p : Program n) (len q l r c : Nat)
 (hl : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (oh ot code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property len q l r c oh ot (.succ code))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let cp := c + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 have hcp := Equations.argumentChild p c .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 let Q := property len q l r c oh ot (.succ code)
 let H := HistoryIteratorSuffix.WitnessProof.secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
 let C := liftTerm (liftTerm code)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 have hh : Hilbert.Local T (ctx+2) [H] (.equal (HistoryKernel.pairCall cp A B) C) := .hypothesis List.mem_cons_self
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p c hc (ctx+2) A B
 have he := localTrans _ _ _ (.base hcons) (localUnary (.succ (.var 0)) _ _ hh)
 obtain ⟨hi⟩ := cons p len q l r c hl hq hc (liftTerm (liftTerm oh)) (liftTerm (liftTerm ot)) A B
 have hout := Hilbert.Local.mp (.mp (.base (transport len q l r c
  (liftTerm (liftTerm oh)) (liftTerm (liftTerm ot)) _ _)) he) (.base hi)
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,C,weakenProperty,liftTerm,renameTerm,substitute,Fin.cases_zero] using
   Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hin⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (HistoryIteratorSuffix.WitnessProof.firstBody cp code) Q ⟨hin⟩
 obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p cp hcp ctx code
 exact ⟨.mp helim hs⟩

theorem relatedCons : RelatedConsTargets.InternalRelatedCons := by
 intro n p len q l r c hl hq hc ctx oh ot code
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := property len q l r c oh ot code
 let E := Formula.equal code .zero
 have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := empty p len q l r c hl hc oh ot
 have hzout := Hilbert.Local.mp (.mp (.base (transport len q l r c oh ot .zero code))
  (HistoryOrder.StepProof.localSym _ _ he)) (.base hz)
 have hzcase : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge hzout)
 let H := HistoryOrder.SupportProof.predBody code
 have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm code) (.succ (.var 0))) := .hypothesis List.mem_cons_self
 obtain ⟨hp⟩ := positive p len q l r c hl hq hc (liftTerm oh) (liftTerm ot) (.var (0 : Fin (ctx+1)))
 have hpout := Hilbert.Local.mp (.mp (.base (transport len q l r c (liftTerm oh) (liftTerm ot) _ _))
  (HistoryOrder.StepProof.localSym _ _ hh)) (.base hp)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,weakenProperty] using Hilbert.Local.finish (Hilbert.Local.discharge hpout)
 obtain ⟨hpcase⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T code
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzcase) hpcase) hcases⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsProof
