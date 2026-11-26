module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RawIndexProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.GapProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport SubstitutionProof WitnessProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
def indexClaim {ctx : Nat} (etag vtag stepTag stag ctag len q l r : Nat)
 (oh ot nh nt tok result raw : Term ctx) : Formula ctx :=
 .imp (RawReflexivityDispatcher.valid vtag raw)
  (.imp (taskRelation l r oh nh)
   (.imp (stackRelation len q l r ot nt)
    (.imp (.equal (call l (oh ::ᵥ nil)) (Term.numeral 2))
     (.imp (.equal (LiteralSyntaxStep.stepCall stepTag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))
      (results stag len q l r (HistoryLookup.consCall ctag nh nt)
       (UniformClosedSubstitutionEmit.emitCall etag (.succ (HistoryLookup.consCall ctag oh ot)) tok raw) result)))))
theorem substClaim {m n : Nat} (s : Fin m → Term n) etag vtag stepTag stag ctag len q l r
 (oh ot nh nt tok result raw : Term m) :
 substituteFormula s (indexClaim etag vtag stepTag stag ctag len q l r oh ot nh nt tok result raw) =
 indexClaim etag vtag stepTag stag ctag len q l r (substitute s oh) (substitute s ot) (substitute s nh)
  (substitute s nt) (substitute s tok) (substitute s result) (substitute s raw) := by
 simp only [indexClaim,substituteFormula,substTask,substStack,substResults,HistoryLookup.DropEquationsProof.substCons,
  LiteralSyntaxStep.stepCall,UniformClosedSubstitutionEmit.emitCall,RawReflexivityDispatcher.valid,
  TwoSol20261113.ReflexivityRecognizer.leafCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  LiteralSyntaxStep.ExpansionSupportProof.substituteNumeral,substitute]
/-- Original positive-gap existential is eliminated internally; no witness
escapes the actual index classification arm. -/
theorem eliminate {n ctx : Nat} (p : Program n)
 (etag vtag stepTag stag ptag ctag atag dtag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nh nt tok result raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.ex (HistoryOrder.SupportProof.predBody
   (HistoryDifference.differenceCall dtag tok (call r (oh ::ᵥ nil)))))
   (indexClaim etag vtag stepTag stag ctag len q l r oh ot nh nt tok result raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.SupportProof.predBody (HistoryDifference.differenceCall dtag tok (call r (oh ::ᵥ nil)))
 let V := RawReflexivityDispatcher.valid vtag (liftTerm raw)
 let A := taskRelation l r (liftTerm oh) (liftTerm nh)
 let B := stackRelation len q l r (liftTerm ot) (liftTerm nt)
 let C := Formula.equal (call l (liftTerm oh ::ᵥ nil)) (Term.numeral 2)
 let E := Formula.equal (LiteralSyntaxStep.stepCall stepTag (.succ (HistoryLookup.consCall ctag (liftTerm oh) (liftTerm ot))) (liftTerm tok)) (.succ (liftTerm result))
 let G := [E,C,B,A,V,H]
 have hvv : Hilbert.Local T (ctx+1) G V := .hypothesis (by simp [G])
 have hh : Hilbert.Local T (ctx+1) G A := .hypothesis (by simp [G])
 have ht : Hilbert.Local T (ctx+1) G B := .hypothesis (by simp [G])
 have hk : Hilbert.Local T (ctx+1) G C := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+1) G E := .hypothesis (by simp [G])
 have hg : Hilbert.Local T (ctx+1) G
  (.equal (HistoryDifference.differenceCall dtag (liftTerm tok) (call r (liftTerm oh ::ᵥ nil))) (.succ (.var 0))) := by
  have h : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
  simpa only [H,HistoryOrder.SupportProof.predBody,liftTerm,renameTerm,
   HistoryDifference.ShiftProof.substituteDifference,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil] using h
 obtain ⟨hout⟩ := RawIndexProof.transport p G etag vtag stepTag stag ptag ctag atag dtag len q l r
  he hv hstep hs hp hc ha hd hl hr (liftTerm oh) (liftTerm ot) (liftTerm nh) (liftTerm nt)
  (liftTerm tok) (liftTerm result) (liftTerm raw) (.var 0) hvv hh ht hk hg hold
 have hb : Derivation T (.imp H (GorbowPACore.weaken
  (indexClaim etag vtag stepTag stag ctag len q l r oh ot nh nt tok result raw))) := by
  rw [GorbowPACore.weaken,substClaim]
  simpa only [G,V,A,B,C,E,indexClaim,liftTerm,renameTerm] using
   hout.discharge.discharge.discharge.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H
  (indexClaim etag vtag stepTag stag ctag len q l r oh ot nh nt tok result raw) ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.GapProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.GapProof
