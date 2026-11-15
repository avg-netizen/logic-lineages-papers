module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.CasesProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.NewStackProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport WitnessProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
def claim {ctx : Nat} (etag vtag stepTag xtag stag ctag len q l r : Nat)
 (oh ot nt tok result added raw : Term ctx) : Formula ctx :=
 .imp (RawReflexivityDispatcher.valid vtag raw)
  (.imp (.equal (LiteralSyntaxStep.expandCall xtag oh tok) (.succ added))
   (.imp (.equal (LiteralSyntaxStep.stepCall stepTag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))
    (results stag len q l r nt (UniformClosedSubstitutionEmit.emitCall etag (.succ (HistoryLookup.consCall ctag oh ot)) tok raw) result)))
theorem substClaim {m n : Nat} (s : Fin m → Term n) etag vtag stepTag xtag stag ctag len q l r
 (oh ot nt tok result added raw : Term m) :
 substituteFormula s (claim etag vtag stepTag xtag stag ctag len q l r oh ot nt tok result added raw) =
 claim etag vtag stepTag xtag stag ctag len q l r (substitute s oh) (substitute s ot) (substitute s nt)
  (substitute s tok) (substitute s result) (substitute s added) (substitute s raw) := by
 simp only [claim,substituteFormula,substResults,LiteralSyntaxStep.expandCall,LiteralSyntaxStep.stepCall,
  UniformClosedSubstitutionEmit.emitCall,RawReflexivityDispatcher.valid,TwoSol20261113.ReflexivityRecognizer.leafCall,
  HistoryLookup.DropEquationsProof.substCons,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenClaim {ctx : Nat} etag vtag stepTag xtag stag ctag len q l r (oh ot nt tok result added raw : Term ctx) :
 GorbowPACore.weaken (claim etag vtag stepTag xtag stag ctag len q l r oh ot nt tok result added raw) =
 claim etag vtag stepTag xtag stag ctag len q l r (liftTerm oh) (liftTerm ot) (liftTerm nt)
  (liftTerm tok) (liftTerm result) (liftTerm added) (liftTerm raw) := by
 rw [GorbowPACore.weaken,substClaim]
 rfl
noncomputable def transportTasks {T : Sentence → Prop} {ctx : Nat} stag len q l r (a b chunk result : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (results stag len q l r a chunk result) (results stag len q l r b chunk result))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (results stag len q l r (.var 0) (liftTerm chunk) (liftTerm result)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substResults,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def transportChunk {T : Sentence → Prop} {ctx : Nat} stag len q l r (nt a b result : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (results stag len q l r nt a result) (results stag len q l r nt b result))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (results stag len q l r (liftTerm nt) (.var 0) (liftTerm result)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substResults,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
theorem eliminate {n ctx : Nat} (p : Program n)
 (etag vtag stepTag xtag stag ptag ctag atag dtag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nt tok result added raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RelatedConsTargets.witnesses len q l r ctag oh ot nt)
   (claim etag vtag stepTag xtag stag ctag len q l r oh ot nt tok result added raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := claim etag vtag stepTag xtag stag ctag len q l r oh ot nt tok result added raw
 let H := RelatedConsWitnessProof.tailBody len q l r ctag (liftTerm oh) (liftTerm ot) (liftTerm nt) (.var (0 : Fin (ctx+1)))
 let OH := liftTerm (liftTerm oh)
 let OT := liftTerm (liftTerm ot)
 let NT := liftTerm (liftTerm nt)
 let TOK := liftTerm (liftTerm tok)
 let RES := liftTerm (liftTerm result)
 let ADD := liftTerm (liftTerm added)
 let RAW := liftTerm (liftTerm raw)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 let V := RawReflexivityDispatcher.valid vtag RAW
 let E := Formula.equal (LiteralSyntaxStep.expandCall xtag OH TOK) (.succ ADD)
 let S := Formula.equal (LiteralSyntaxStep.stepCall stepTag (.succ (HistoryLookup.consCall ctag OH OT)) TOK) (.succ RES)
 let G := [S,E,V,H]
 have hw : Hilbert.Local T (ctx+2) G H := .hypothesis (by simp [G])
 have heq := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hw
 have hh := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrel
 have ht := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrel
 have hvv : Hilbert.Local T (ctx+2) G V := .hypothesis (by simp [G])
 have hex : Hilbert.Local T (ctx+2) G E := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+2) G S := .hypothesis (by simp [G])
 obtain ⟨hout⟩ := CasesProof.classified p G etag vtag stepTag xtag stag ptag ctag atag dtag len q l r
  he hv hstep hx hs hp hc ha hd hlen hq hl hr OH OT A B TOK RES ADD RAW hvv hh ht hex hold
 have hfinal := Hilbert.Local.mp (.mp (.base (transportTasks stag len q l r (HistoryLookup.consCall ctag A B) NT
  (UniformClosedSubstitutionEmit.emitCall etag (.succ (HistoryLookup.consCall ctag OH OT)) TOK RAW) RES))
  (HistoryOrder.StepProof.localSym _ _ heq)) hout
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  dsimp only [Q]
  rw [weakenClaim,weakenClaim]
  simpa only [Q,claim,OH,OT,NT,TOK,RES,ADD,RAW,G,S,E,V] using
   hfinal.discharge.discharge.discharge.discharge.finish
 obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 exact HBQuantifier.existentialElimination T (RelatedConsWitnessProof.headBody len q l r ctag oh ot nt) Q ⟨hinner⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.NewStackProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.NewStackProof
