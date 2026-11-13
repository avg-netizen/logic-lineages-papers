module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Frame FusionAlgebraProof
noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} itag ltag ptag rtag atag (raw tasks out suffix : Term ctx) :
 Derivation T (.imp (allTasks itag ltag ptag rtag atag raw out suffix) (property itag ltag ptag rtag atag raw tasks out suffix)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (property itag ltag ptag rtag atag (liftTerm raw) (.var 0) (liftTerm out) (liftTerm suffix)) tasks)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,allTasks] using h
noncomputable def boundedInstance {T : Sentence → Prop} {ctx : Nat} itag ltag ptag rtag atag (bound raw out suffix : Term ctx) :
 Derivation T (.imp (bounded itag ltag ptag rtag atag bound out suffix)
  (.imp (HistoryBounds.weakBound raw bound) (allTasks itag ltag ptag rtag atag raw out suffix))) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound)) (allTasks itag ltag ptag rtag atag (.var 0) (liftTerm out) (liftTerm suffix))) raw)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substituteFormula,
  HistoryBounds.SupportProof.substWeak,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,bounded] using h
noncomputable def transportAll {T : Sentence → Prop} {ctx : Nat} itag ltag ptag rtag atag (a b out suffix : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (allTasks itag ltag ptag rtag atag a out suffix) (allTasks itag ltag ptag rtag atag b out suffix))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (allTasks itag ltag ptag rtag atag (.var 0) (liftTerm out) (liftTerm suffix)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

section
variable {n ctx : Nat} (p : Program n) (itag ltag ptag rtag atag : Nat)
variable (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
variable (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
include hi hl hp hr
theorem nilFrame (tasks out suffix : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (property itag ltag ptag rtag atag .zero tasks out suffix)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (scanState itag ltag ptag rtag .zero (.succ tasks)) (.succ out)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hfirst⟩ := StateRecursionProof.nil p itag ltag ptag rtag hi hl hp hr (.succ tasks)
 have he : Hilbert.Local T ctx [H] (.equal tasks out) := .mp (.base (.arithmetic (.succInjective _ _)))
  (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hfirst)) hh)
 have happ := LiteralSyntaxFrame.AppendSupport.binary atag tasks suffix out suffix he (.base (.logical (.reflexive suffix)))
 obtain ⟨hfinal⟩ := StateRecursionProof.nil p itag ltag ptag rtag hi hl hp hr (.succ (HistoryAppend.appendCall atag tasks suffix))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hfinal) (localUnary (.succ (.var 0)) _ _ happ)))⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameSupportProof
