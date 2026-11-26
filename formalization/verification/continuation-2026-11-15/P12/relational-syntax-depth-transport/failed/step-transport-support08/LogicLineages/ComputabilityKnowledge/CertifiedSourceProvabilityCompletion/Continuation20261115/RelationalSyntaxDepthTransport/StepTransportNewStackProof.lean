module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportNewStackProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open StepTransportWitnessProof

def claim {ctx : Nat} (stag etag ctag len q l r : Nat) (oh ot nt tok result added : Term ctx) : Formula ctx :=
 .imp (.equal (LiteralSyntaxStep.expandCall etag oh tok) (.succ added))
  (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))
   (StepTransportTargets.witnesses stag len q l r nt tok result))
theorem substClaim {m n : Nat} (s : Fin m → Term n) stag etag ctag len q l r (oh ot nt tok result added : Term m) :
 substituteFormula s (claim stag etag ctag len q l r oh ot nt tok result added) =
 claim stag etag ctag len q l r (substitute s oh) (substitute s ot) (substitute s nt)
  (substitute s tok) (substitute s result) (substitute s added) := by
 simp only [claim,substituteFormula,substWitnesses,LiteralSyntaxStep.expandCall,LiteralSyntaxStep.stepCall,
  HistoryLookup.DropEquationsProof.substCons,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenClaim {ctx : Nat} stag etag ctag len q l r (oh ot nt tok result added : Term ctx) :
 GorbowPACore.weaken (claim stag etag ctag len q l r oh ot nt tok result added) =
 claim stag etag ctag len q l r (liftTerm oh) (liftTerm ot) (liftTerm nt) (liftTerm tok) (liftTerm result) (liftTerm added) := by
 rw [GorbowPACore.weaken,substClaim]
 rfl
noncomputable def transportWitness {T : Sentence → Prop} {ctx : Nat} stag len q l r (a b tok result : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (StepTransportTargets.witnesses stag len q l r a tok result)
  (StepTransportTargets.witnesses stag len q l r b tok result))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (StepTransportTargets.witnesses stag len q l r (.var 0) (liftTerm tok) (liftTerm result)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substWitnesses,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
/-- Both recovered NEW stack witnesses are eliminated in the unchanged calculus. -/
theorem eliminateNewStack {n ctx : Nat} (p : Program n) (stag etag ptag ctag atag dtag len q l r : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nt tok result added : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RelatedConsTargets.witnesses len q l r ctag oh ot nt)
   (claim stag etag ctag len q l r oh ot nt tok result added))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := claim stag etag ctag len q l r oh ot nt tok result added
 let H := RelatedConsWitnessProof.tailBody len q l r ctag (liftTerm oh) (liftTerm ot) (liftTerm nt) (.var (0 : Fin (ctx+1)))
 let OH := liftTerm (liftTerm oh)
 let OT := liftTerm (liftTerm ot)
 let NT := liftTerm (liftTerm nt)
 let TOK := liftTerm (liftTerm tok)
 let RES := liftTerm (liftTerm result)
 let ADD := liftTerm (liftTerm added)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 let E := Formula.equal (LiteralSyntaxStep.expandCall etag OH TOK) (.succ ADD)
 let S := Formula.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag OH OT)) TOK) (.succ RES)
 let G := [S,E,H]
 have hw : Hilbert.Local T (ctx+2) G H := .hypothesis (by simp [G])
 have heq := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hw
 have hh := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrel
 have ht := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrel
 have hex : Hilbert.Local T (ctx+2) G E := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+2) G S := .hypothesis (by simp [G])
 obtain ⟨hout⟩ := StepTransportCasesProof.classifiedTransport p G stag etag ptag ctag atag dtag len q l r
  hs he hp hc ha hd hlen hq hl hr OH OT A B TOK RES ADD hh ht hex hold
 have hfinal := Hilbert.Local.mp (.mp (.base (transportWitness stag len q l r
  (HistoryLookup.consCall ctag A B) NT TOK RES)) (HistoryOrder.StepProof.localSym _ _ heq)) hout
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,weakenClaim,claim,OH,OT,NT,TOK,RES,ADD,G,S,E] using
   hfinal.discharge.discharge.discharge.finish
 obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨houter⟩ := HBQuantifier.existentialElimination T
  (RelatedConsWitnessProof.headBody len q l r ctag oh ot nt) Q ⟨hinner⟩
 exact ⟨houter⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportNewStackProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportNewStackProof
