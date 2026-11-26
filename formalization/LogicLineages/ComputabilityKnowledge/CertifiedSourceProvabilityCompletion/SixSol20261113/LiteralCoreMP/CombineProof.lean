module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.AcceptedRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.CombineProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralValidatedMPRun LiteralRawMP LiteralMPRun LiteralCheckerAcceptance TailProof

-- One symbolic two-existential elimination; supplied body is an actual internal derivation.
theorem twoTails (T : Sentence → Prop) {ctx : Nat} ptag ctag
 (stateI stateA context rawI rawA : Term ctx) (Q : Formula ctx)
 (h : Derivation T (.imp
   (GorbowPACore.weaken (tailBody ptag ctag stateI context rawI))
   (.imp (tailBody ptag ctag (liftTerm stateA) (liftTerm context) (liftTerm rawA))
     (GorbowPACore.weaken (GorbowPACore.weaken Q))))) :
 Nonempty (Derivation T (.imp (tailWitness ptag ctag stateI context rawI)
  (.imp (tailWitness ptag ctag stateA context rawA) Q))) := by
 let A := GorbowPACore.weaken (tailBody ptag ctag stateI context rawI)
 let B := tailBody ptag ctag (liftTerm stateA) (liftTerm context) (liftTerm rawA)
 let R := GorbowPACore.weaken (GorbowPACore.weaken Q)
 have ha : Hilbert.Local T (ctx+1+1) [A,B] A := .hypothesis List.mem_cons_self
 have hb : Hilbert.Local T (ctx+1+1) [A,B] B := .hypothesis (by simp)
 have r : Hilbert.Local T (ctx+1+1) [A,B] R := .mp (.mp (.base h) ha) hb
 have rev : Derivation T (.imp B (GorbowPACore.weaken
   (.imp (tailBody ptag ctag stateI context rawI) (GorbowPACore.weaken Q)))) :=
  Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge r))
 obtain ⟨he⟩ := HBQuantifier.existentialElimination T B
   (.imp (tailBody ptag ctag stateI context rawI) (GorbowPACore.weaken Q)) ⟨rev⟩
 let A1 := tailBody ptag ctag stateI context rawI
 let B1 := tailWitness ptag ctag (liftTerm stateA) (liftTerm context) (liftTerm rawA)
 have ha1 : Hilbert.Local T (ctx+1) [B1,A1] A1 := .hypothesis (by simp)
 have hb1 : Hilbert.Local T (ctx+1) [B1,A1] B1 := .hypothesis List.mem_cons_self
 have r1 : Hilbert.Local T (ctx+1) [B1,A1] (GorbowPACore.weaken Q) := .mp (.mp (.base he) hb1) ha1
 have rev1 : Derivation T (.imp A1 (GorbowPACore.weaken
   (.imp (tailWitness ptag ctag stateA context rawA) Q))) := by
  simpa only [A1,B1,GorbowPACore.weaken,substituteFormula,substTail,liftTerm,renameTerm] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge r1))
 exact HBQuantifier.existentialElimination T A1 _ ⟨rev1⟩

theorem internalCoreMP : Targets.InternalCoreMP := by
 intro l a x n p itag ltag atag ptag ctag dtag droptag rtag dispatcherTag hi hl ha hp hc hd hdrop hr ht
   mtag qtag hm hq ctx context phi psi imp ant index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := Formula.equal (coreCall qtag index fuel context (.add psi psi)
   (certificate mtag context psi imp ant)) (.succ .zero)
 let rawI := implicationRaw atag ctag phi psi
 let stateI := runCall itag ptag index fuel imp
 let stateA := runCall itag ptag index fuel ant
 let lift2 : Term ctx → Term (ctx+1+1) := fun t => liftTerm (liftTerm t)
 obtain ⟨h⟩ := LiteralValidatedMPRun.RunProof.internalCoreAcceptance l a x n p itag ltag atag ptag ctag dtag droptag rtag dispatcherTag
   hi hl ha hp hc hd hdrop hr ht mtag qtag hm hq (ctx+1+1)
   (lift2 context) (lift2 phi) (lift2 psi) (lift2 imp) (lift2 ant) (.var (Fin.succ (0 : Fin (ctx+1)))) (.var 0) (lift2 index) (lift2 fuel)
 have hh : Derivation T (.imp (GorbowPACore.weaken (tailBody ptag ctag stateI context rawI))
   (.imp (tailBody ptag ctag (liftTerm stateA) (liftTerm context) (liftTerm phi))
    (GorbowPACore.weaken (GorbowPACore.weaken Q)))) := by
  let A := GorbowPACore.weaken (tailBody ptag ctag stateI context rawI)
  let B := tailBody ptag ctag (liftTerm stateA) (liftTerm context) (liftTerm phi)
  have hA : Hilbert.Local T (ctx+1+1) [B,A] A := .hypothesis (by simp)
  have hB : Hilbert.Local T (ctx+1+1) [B,A] B := .hypothesis List.mem_cons_self
  have hpair := Hilbert.Local.mp (.mp (.base (.logical (.andIntro A B))) hA) hB
  have h' : Derivation T (.imp (.conj A B) (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
   simpa only [A,B,Q,stateI,stateA,rawI,lift2,tailBody,GorbowPACore.weaken,substituteFormula,
    inputRuns,implicationHistory,antecedentHistory,implicationEntry,antecedentEntry,
    runCall,HistoryRunSplice.run,HistoryRunSplice.state,LiteralCheckerAuxiliaries.successfulState,
    SixSol20261112.HistoryMachine.iterationCall,coreCall,certificate,implicationRaw,
    HistoryAppend.appendCall,HistoryLookup.consCall,HistoryKernel.pairCall,Logic.substCall,
    liftTerm,renameTerm,Term.numeral,substitute,List.Vector.map_cons,List.Vector.map_nil] using h
  exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.base h') hpair)))
 obtain ⟨hcombine⟩ := twoTails T ptag ctag stateI stateA context rawI phi Q hh
 obtain ⟨hI⟩ := AcceptedRunProof.internalAcceptedRun l a x n p qtag itag ptag ctag dtag droptag hq hi hp hc hd hdrop ctx context rawI imp index fuel
 obtain ⟨hA⟩ := AcceptedRunProof.internalAcceptedRun l a x n p qtag itag ptag ctag dtag droptag hq hi hp hc hd hdrop ctx context phi ant index fuel
 let H := inputAcceptance qtag atag ctag context phi psi imp ant index fuel
 have hhyp : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hri := Hilbert.Local.mp (.base hI) (.mp (.base (.logical (.andLeft _ _))) hhyp)
 have hra := Hilbert.Local.mp (.base hA) (.mp (.base (.logical (.andRight _ _))) hhyp)
 have hcombine' : Derivation T (.imp (successfulRun itag ptag ctag context rawI imp index fuel)
   (.imp (successfulRun itag ptag ctag context phi ant index fuel) Q)) := by
  simpa only [stateI,stateA,AcceptedRunProof.tailRun] using hcombine
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base hcombine') hri) hra))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.CombineProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.CombineProof
