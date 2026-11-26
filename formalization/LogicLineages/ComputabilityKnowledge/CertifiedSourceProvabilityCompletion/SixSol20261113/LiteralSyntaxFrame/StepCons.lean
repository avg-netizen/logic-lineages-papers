module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepCons
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralSyntaxStep
open HistoryAppend.PreserveSupportProof (substAppend)

def property {ctx : Nat} (stag atag : Nat) (tasks out suffix token : Term ctx) : Formula ctx :=
 .imp (.equal (stepCall stag (.succ tasks) token) (.succ out))
   (.equal (stepCall stag (.succ (HistoryAppend.appendCall atag tasks suffix)) token)
     (.succ (HistoryAppend.appendCall atag out suffix)))
theorem substStep {m n : Nat} (s : Fin m → Term n) tag (state token : Term m) :
 substitute s (stepCall tag state token) = stepCall tag (substitute s state) (substitute s token) := by
 simp only [stepCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substProperty {m n : Nat} (s : Fin m → Term n) stag atag (tasks out suffix token : Term m) :
 substituteFormula s (property stag atag tasks out suffix token) = property stag atag (substitute s tasks) (substitute s out) (substitute s suffix) (substitute s token) := by
 simp only [property,substituteFormula,substStep,substAppend,substitute]
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} stag atag (a b out suffix token : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (property stag atag a out suffix token) (property stag atag b out suffix token))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property stag atag (.var 0) (liftTerm out) (liftTerm suffix) (liftTerm token)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def stepCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} stag (a b token : Term ctx)
 (h : Hilbert.Local T ctx G (.equal a b)) :
 Hilbert.Local T ctx G (.equal (stepCall stag (.succ a) token) (stepCall stag (.succ b) token)) := by
 have e := localUnary (stepCall stag (.succ (.var 0)) (liftTerm token)) a b h
 simpa only [substStep,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using e

theorem expanded {n ctx : Nat} (p : Program n) (stag etag atag ctag ltag rtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩) (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (head tail out suffix token added : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (expandCall etag head token) (.succ added))
  (property stag atag (HistoryLookup.consCall ctag head tail) out suffix token))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := Formula.equal (expandCall etag head token) (.succ added)
 let H := Formula.equal (stepCall stag (.succ (HistoryLookup.consCall ctag head tail)) token) (.succ out)
 let G := [H,E]
 have he0 : Hilbert.Local T ctx G E := .hypothesis (by simp [G])
 have hh : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
 obtain ⟨hstep⟩ := StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx head tail token added
 have first := Hilbert.Local.mp (.base hstep) he0
 have hi : Hilbert.Local T ctx G (.equal out (HistoryAppend.appendCall atag added tail)) :=
  .mp (.base (.arithmetic (.succInjective _ _))) (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hh) first)
 obtain ⟨happ⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx head tail suffix
 have hstart := stepCongruence stag _ _ token (Hilbert.Local.base (Gamma := G) happ)
 obtain ⟨hstep2⟩ := StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx head (HistoryAppend.appendCall atag tail suffix) token added
 have second := Hilbert.Local.mp (.base hstep2) he0
 obtain ⟨hassoc⟩ := AppendProof.internalAppendAssociativity n p atag ctag ltag rtag ha hc hl hr ctx added tail suffix
 have houtput := AppendSupport.binary atag out suffix _ suffix hi (.base (.logical (.reflexive suffix)))
 have hout := localTrans _ _ _ houtput (.base hassoc)
 have final := localTrans _ _ _ hstart (localTrans _ _ _ second (HistoryOrder.StepProof.localSym _ _ (localUnary (.succ (.var 0)) _ _ hout)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge final))⟩
/-- Eliminates the expansion premise by PA zero/successor cases. -/
theorem consFrame {n ctx : Nat} (p : Program n) (stag etag atag ctag ltag rtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩) (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (head tail out suffix token : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property stag atag (HistoryLookup.consCall ctag head tail) out suffix token)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let e := expandCall etag head token
 let Q := property stag atag (HistoryLookup.consCall ctag head tail) out suffix token
 let E := Formula.equal e .zero
 let H := Formula.equal (stepCall stag (.succ (HistoryLookup.consCall ctag head tail)) token) (.succ out)
 have he0 : Hilbert.Local T ctx [H,E] E := .hypothesis (by simp)
 have hh : Hilbert.Local T ctx [H,E] H := .hypothesis List.mem_cons_self
 obtain ⟨hbad⟩ := StepCases.rejectedCons p stag etag ctag hs he hc head tail token
 have hz := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hh) (.mp (.base hbad) he0)
 have contradiction := Hilbert.Local.explosion
   (.equal (stepCall stag (.succ (HistoryAppend.appendCall atag (HistoryLookup.consCall ctag head tail) suffix)) token)
    (.succ (HistoryAppend.appendCall atag out suffix))) hz (.base (.arithmetic (.succNotZero out)))
 have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge contradiction))
 let P := HistoryOrder.SupportProof.predBody e
 obtain ⟨hpositive⟩ := expanded p stag etag atag ctag ltag rtag hs he ha hc hl hr
   (liftTerm head) (liftTerm tail) (liftTerm out) (liftTerm suffix) (liftTerm token) (.var (0 : Fin (ctx+1)))
 have hp : Derivation T (.imp P (GorbowPACore.weaken Q)) := by
  simpa only [P,Q,e,HistoryOrder.SupportProof.predBody,GorbowPACore.weaken,substProperty,
   expandCall,HistoryLookup.consCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
   substitute,liftTerm,renameTerm] using hpositive
 obtain ⟨hex⟩ := HBQuantifier.existentialElimination T P Q ⟨hp⟩
 obtain ⟨hsplit⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T e
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hex) hsplit⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepCons
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepCons
