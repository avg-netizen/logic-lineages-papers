module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.ConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.NewResultProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport InvariantProof BoundProof
open UniformSubstitutionChunkTransport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
def claim {ctx : Nat} (ftag vtag stepTag stag ptag ctag len q l r : Nat)
 (token tokens start raw oldTasks current out oldResult nextOld : Term ctx) : Formula ctx :=
 .imp (allStates ftag vtag stag ptag len q l r tokens start raw)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.imp (.equal (LiteralSyntaxScan.scanCall stag start out) (.succ current))
    (.imp (.equal (LiteralSyntaxScan.scanCall stag oldTasks (HistoryLookup.consCall ctag token tokens)) (.succ oldResult))
     (.imp (.equal (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token) (.succ nextOld))
      (results stag len q l r start (outputAt ftag ptag r (HistoryLookup.consCall ctag token tokens) oldTasks out raw) oldResult)))))
theorem substClaim {m n : Nat} (s : Fin m → Term n) ftag vtag stepTag stag ptag ctag len q l r
 (token tokens start raw oldTasks current out oldResult nextOld : Term m) :
 substituteFormula s (claim ftag vtag stepTag stag ptag ctag len q l r token tokens start raw oldTasks current out oldResult nextOld) =
 claim ftag vtag stepTag stag ptag ctag len q l r (substitute s token) (substitute s tokens)
  (substitute s start) (substitute s raw) (substitute s oldTasks) (substitute s current) (substitute s out)
  (substitute s oldResult) (substitute s nextOld) := by
 simp only [claim,substituteFormula,substAllStates,InvariantProof.substOutput,
  UniformSubstitutionChunkTransport.WitnessProof.substResults,RawReflexivityDispatcher.valid,
  TwoSol20261113.ReflexivityRecognizer.leafCall,LiteralSyntaxScan.scanCall,LiteralSyntaxStep.stepCall,
  HistoryLookup.DropEquationsProof.substCons,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute]
/-- Eliminate the existential new intermediate stack supplied by actual chunk
transport, carrying all changing accumulator terms under the binder. -/
theorem eliminate {n ctx : Nat} (p : Program n) (ftag etag vtag stepTag stag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (token tokens start raw oldTasks current out oldResult nextOld : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (results stag len q l r current (UniformClosedSubstitutionEmit.emitCall etag (.succ oldTasks) token raw) nextOld)
   (claim ftag vtag stepTag stag ptag ctag len q l r token tokens start raw oldTasks current out oldResult nextOld))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := claim ftag vtag stepTag stag ptag ctag len q l r token tokens start raw oldTasks current out oldResult nextOld
 let H := resultBody stag len q l r (liftTerm current)
  (liftTerm (UniformClosedSubstitutionEmit.emitCall etag (.succ oldTasks) token raw)) (liftTerm nextOld) (.var (0 : Fin (ctx+1)))
 let I := allStates ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw)
 let V := RawReflexivityDispatcher.valid vtag (liftTerm raw)
 let P := Formula.equal (LiteralSyntaxScan.scanCall stag (liftTerm start) (liftTerm out)) (.succ (liftTerm current))
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag (liftTerm oldTasks) (HistoryLookup.consCall ctag (liftTerm token) (liftTerm tokens))) (.succ (liftTerm oldResult))
 let E := Formula.equal (LiteralSyntaxStep.stepCall stepTag (.succ (liftTerm oldTasks)) (liftTerm token)) (.succ (liftTerm nextOld))
 let G := [E,S,P,V,I,H]
 have hi : Hilbert.Local T (ctx+1) G I := .hypothesis (by simp [G])
 have hv : Hilbert.Local T (ctx+1) G V := .hypothesis (by simp [G])
 have hprefix : Hilbert.Local T (ctx+1) G P := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+1) G S := .hypothesis (by simp [G])
 have hst : Hilbert.Local T (ctx+1) G E := .hypothesis (by simp [G])
 have hchunk : Hilbert.Local T (ctx+1) G
  (resultBody stag len q l r (liftTerm current)
   (UniformClosedSubstitutionEmit.emitCall etag (.succ (liftTerm oldTasks)) (liftTerm token) (liftTerm raw))
   (liftTerm nextOld) (.var 0)) := by
  have h : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
  simpa only [H,liftTerm,renameTerm,UniformClosedSubstitutionEmit.emitCall,
   Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute] using h
 obtain ⟨hout⟩ := ConsProof.consAt p G ftag etag vtag stepTag stag ptag ctag atag len q l r hf he hstep hs hp hc ha
  (liftTerm token) (liftTerm tokens) (liftTerm start) (liftTerm raw) (liftTerm oldTasks) (liftTerm current)
  (liftTerm out) (liftTerm oldResult) (liftTerm nextOld) (.var 0) hi hv hprefix hold hst hchunk
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  rw [GorbowPACore.weaken,substClaim]
  simpa only [Q,claim,I,V,P,S,E,G,liftTerm,renameTerm] using
   hout.discharge.discharge.discharge.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H Q ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.NewResultProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.NewResultProof
