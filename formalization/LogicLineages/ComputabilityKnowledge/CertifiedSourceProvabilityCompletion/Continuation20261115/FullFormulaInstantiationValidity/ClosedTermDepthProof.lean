module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Empty stacks are related internally: the quantified lookup premise is
impossible by the original nil lookup equation, including every raw index. -/
theorem emptyRelation {n ctx : Nat} (p : Program n) (len q l r : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (stackRelation (ctx := ctx) len q l r .zero .zero)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let i : Term (ctx+2) := .var 1
 let t : Term (ctx+2) := .var 0
 let H := Formula.equal (HistoryLookup.lookupCall q i .zero) (.succ t)
 let Q := RelationLogicProof.witness q l r (.zero : Term (ctx+2)) i t
 have hh : Hilbert.Local T (ctx+2) [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hnil⟩ := HistoryLookup.LookupProof.internalLookupNil n p q hq (ctx+2) i
 have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hh) (.base hnil)
 have hout := Hilbert.Local.explosion Q hbad (.base (.arithmetic (.succNotZero t)))
 have hall : Derivation T (.all (entryRelation q l r (.zero : Term (ctx+1)) .zero (.var 0))) := by
  simpa only [entryRelation,RelationLogicProof.witness,RelationLogicProof.witnessBody,
   H,Q,i,t,liftTerm,renameTerm,substitute,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] using
   (Derivation.generalize (Derivation.generalize hout.discharge.finish))
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) (.logical (.reflexive _))) hall⟩
/-- Closed term runtime validity transports to arbitrary internal binder bounds. -/
theorem closedTermAtAnyDepth : ClosedTermDepthTargets.InternalClosedTermAtAnyDepth := by
 intro n p vtag stag ptag ctag atag hv hs hp hc ha ctx bound raw
 obtain ⟨len,q,l,r,hlen,hq,hl,hr⟩ := InstallationProof.auxiliaryTags p stag atag hs ha
 let T := GorbowPRNumeralCalculation.Theory p
 have hbound : Derivation T (HistoryBounds.weakBound (.zero : Term ctx) bound) :=
  .mp (HistoryBounds.SupportProof.weakIntro .zero bound bound) (Support.equalitySymmetry _ _ (zeroLeft bound))
 obtain ⟨hpair⟩ := ConstructorTaskProof.taskPair p ptag l r 0 hp hl hr (.zero : Term ctx) bound
 have hhead := Derivation.mp hpair hbound
 obtain ⟨hempty⟩ := emptyRelation (ctx := ctx) p len q l r hq
 obtain ⟨hcons⟩ := ConsProof.consRelated p len q l r ctag hlen hq hc
  (LiteralSyntaxStep.taskCall ptag 0 (.zero : Term ctx)) .zero (LiteralSyntaxStep.taskCall ptag 0 bound) .zero
 have hrel := Derivation.mp hcons (.mp (.mp (.logical (.andIntro _ _)) hhead) hempty)
 obtain ⟨hscan⟩ := ClosedScanProof.closedScanTransport n p stag len q ptag ctag atag l r
  hs hlen hq hp hc ha hl hr ctx
  (ClosedTermDepthTargets.tasks ptag ctag .zero) (ClosedTermDepthTargets.tasks ptag ctag bound) raw
 obtain ⟨hvalid⟩ := RawReflexivityDispatcher.TermSoundProof.sound p vtag stag ptag ctag hv hs hp hc raw
 exact ⟨Hilbert.compose (.mp hscan hrel) hvalid⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthProof
