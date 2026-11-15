module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ActualConsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.RelatedConsStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.NewStackProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport BoundProof InvariantProof

def claim {ctx : Nat} (ftag stag xtag ptag ctag atag len q l r : Nat)
 (oh ot nt tok tokens raw rest out added : Term ctx) : Formula ctx :=
 .imp (allStates ftag stag ptag ctag atag len q l r tokens raw)
  (.imp (.equal (LiteralSyntaxStep.expandCall xtag oh tok) (.succ added))
   (property ftag stag ptag ctag atag len q l r (HistoryLookup.consCall ctag tok tokens) raw
    (HistoryLookup.consCall ctag oh ot) nt rest out))
theorem substClaim {m n : Nat} (s : Fin m → Term n) ftag stag xtag ptag ctag atag len q l r
 (oh ot nt tok tokens raw rest out added : Term m) :
 substituteFormula s (claim ftag stag xtag ptag ctag atag len q l r oh ot nt tok tokens raw rest out added) =
 claim ftag stag xtag ptag ctag atag len q l r (substitute s oh) (substitute s ot) (substitute s nt)
  (substitute s tok) (substitute s tokens) (substitute s raw) (substitute s rest) (substitute s out) (substitute s added) := by
 simp only [claim,substituteFormula,substAllStates,InvariantProof.substProperty,
  LiteralSyntaxStep.expandCall,HistoryLookup.DropEquationsProof.substCons,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenClaim {ctx : Nat} ftag stag xtag ptag ctag atag len q l r
 (oh ot nt tok tokens raw rest out added : Term ctx) :
 GorbowPACore.weaken (claim ftag stag xtag ptag ctag atag len q l r oh ot nt tok tokens raw rest out added) =
 claim ftag stag xtag ptag ctag atag len q l r (liftTerm oh) (liftTerm ot) (liftTerm nt)
  (liftTerm tok) (liftTerm tokens) (liftTerm raw) (liftTerm rest) (liftTerm out) (liftTerm added) := by
 rw [GorbowPACore.weaken,substClaim]
 rfl
/-- Existential new head/tail are discharged inside the original internal logic. -/
theorem eliminate {n ctx : Nat} (p : Program n)
 (ftag stag stepTag etag xtag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (dtag : Nat) (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (oh ot nt tok tokens raw rest out added : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RelatedConsTargets.witnesses len q l r ctag oh ot nt)
   (claim ftag stag xtag ptag ctag atag len q l r oh ot nt tok tokens raw rest out added))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := claim ftag stag xtag ptag ctag atag len q l r oh ot nt tok tokens raw rest out added
 let H := RelatedConsWitnessProof.tailBody len q l r ctag (liftTerm oh) (liftTerm ot) (liftTerm nt) (.var (0 : Fin (ctx+1)))
 let OH := liftTerm (liftTerm oh)
 let OT := liftTerm (liftTerm ot)
 let NT := liftTerm (liftTerm nt)
 let TOK := liftTerm (liftTerm tok)
 let TOKENS := liftTerm (liftTerm tokens)
 let RAW := liftTerm (liftTerm raw)
 let REST := liftTerm (liftTerm rest)
 let OUT := liftTerm (liftTerm out)
 let ADD := liftTerm (liftTerm added)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 let OLD := HistoryLookup.consCall ctag OH OT
 let NEW := HistoryLookup.consCall ctag A B
 let INPUT := HistoryLookup.consCall ctag TOK TOKENS
 let IH := allStates ftag stag ptag ctag atag len q l r TOKENS RAW
 let E := Formula.equal (LiteralSyntaxStep.expandCall xtag OH TOK) (.succ ADD)
 let ENT := EntriesLogic.entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) OLD
 let REL := stackRelation len q l r OLD NEW
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag OLD INPUT) (.succ .zero)
 let G := [S,REL,ENT,E,IH,H]
 have hih : Hilbert.Local T (ctx+2) G IH := .hypothesis (by simp [G])
 have hex : Hilbert.Local T (ctx+2) G E := .hypothesis (by simp [G])
 have hent : Hilbert.Local T (ctx+2) G ENT := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T (ctx+2) G REL := .hypothesis (by simp [G])
 have hscan : Hilbert.Local T (ctx+2) G S := .hypothesis (by simp [G])
 obtain ⟨hout⟩ := ActualConsProof.actual p G ftag stag stepTag etag xtag ptag ctag atag len q l r
  hf hs hst he hx hp hc ha hlen hq hl hr dtag hd TOK TOKENS RAW OH OT A B REST OUT ADD hih hent hrel hex hscan
 have hpnew : Hilbert.Local T (ctx+2) [E,IH,H]
  (property ftag stag ptag ctag atag len q l r INPUT RAW OLD NEW REST OUT) :=
  hout.discharge.discharge.discharge
 have hw : Hilbert.Local T (ctx+2) [E,IH,H] H := .hypothesis (by simp)
 have heq := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hfinal := Hilbert.Local.mp (.mp (.base (TransportProof.newTasks ftag stag ptag ctag atag len q l r
  INPUT RAW OLD NEW NT REST OUT)) (HistoryOrder.StepProof.localSym _ _ heq)) hpnew
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  dsimp only [Q]
  rw [weakenClaim,weakenClaim]
  simpa only [claim,OH,OT,NT,TOK,TOKENS,RAW,REST,OUT,ADD,OLD,INPUT,IH,E] using
   hfinal.discharge.discharge.discharge.finish
 obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 exact HBQuantifier.existentialElimination T (RelatedConsWitnessProof.headBody len q l r ctag oh ot nt) Q ⟨hinner⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.NewStackProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.NewStackProof
