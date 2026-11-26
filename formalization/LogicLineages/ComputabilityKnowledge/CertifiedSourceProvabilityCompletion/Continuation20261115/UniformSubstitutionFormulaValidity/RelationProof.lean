module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.LengthZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.RelationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open UniformSubstitutionChunkTransport
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

/-- Exact symbolic-depth singleton formula stacks, using the capture-aware
chunk task relation, not a cast of the earlier depth relation. -/
theorem singleton {n ctx : Nat} (p : Program n) (len q l r ptag ctag : Nat)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (depth : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (stackRelation len q l r
   (LiteralSyntaxValidator.FormulaBindingProof.taskList ptag ctag (.succ depth))
   (LiteralSyntaxValidator.FormulaBindingProof.taskList ptag ctag depth))) := by
 obtain ⟨hhead⟩ := TaskProof.formula p [] ptag l r hp hl hr depth
 obtain ⟨hempty⟩ := emptyRelation (ctx := ctx) p len q l r hq
 obtain ⟨hcons⟩ := ConsProof.consRelated p len q l r ctag hlen hq hc
  (LiteralSyntaxStep.taskCall ptag 1 (.succ depth)) .zero
  (LiteralSyntaxStep.taskCall ptag 1 depth) .zero
 exact ⟨.mp hcons (.mp (.mp (.logical (.andIntro _ _)) hhead.finish) hempty)⟩

/-- Only length equality is extracted; the two different task relations are
never identified. The original internal length-zero theorem pays decoding. -/
theorem emptyResult {n ctx : Nat} (p : Program n) (len q l r ctag : Nat)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (tasks : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (stackRelation len q l r .zero tasks) (.equal tasks .zero))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := stackRelation len q l r (.zero : Term ctx) tasks
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 obtain ⟨hnil⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p len hlen ctx
 have hz := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) (.base hnil)
 obtain ⟨hzero⟩ := RelationalSyntaxDepthTransport.LengthZeroProof.allCodes p len ctag hlen hc tasks
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hzero) hz))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.RelationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.RelationProof
