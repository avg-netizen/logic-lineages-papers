module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.EntryWitnessProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ConsInjectiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ActiveStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel.EntryProof HistoryKernel.TransitionEquationsProof

theorem activeStep {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (history line rest index fuel context raw tail : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (.equal (HistoryKernel.kernelCall (kernelTag itag)
     (HistoryKernel.activeState ptag ctag history line rest) index fuel)
     (HistoryKernel.pairCall ptag (.succ (HistoryLookup.consCall ctag
       (HistoryKernel.pairCall ptag context raw) tail)) rest))
     (topWitness (validityTag itag v l a x) leftTag rightTag context raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let kt := kernelTag itag
 let st := someTag kt v l a x
 let et := entryWrapper st
 let target := HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail
 let E := Formula.equal (HistoryKernel.kernelCall kt
     (HistoryKernel.activeState ptag ctag history line rest) index fuel)
     (HistoryKernel.pairCall ptag (.succ target) rest)
 have hk := HistoryRunSplice.IdleProof.kernelInstalled p itag v l a x hi
 have hs := someInstalled p kt v l a x hk
 have hext := Equations.argumentChild p st .succ (fun _ : Fin 1 => HistoryKernel.extendedHistory) hs 0
 have he := Equations.argumentChild p (extendedWrapper st) HistoryCodec.cons extendedArguments hext 0
 have hout := outputConsInstalled p st hs
 obtain ⟨hparts⟩ := HistoryKernel.SuccessProof.successfulParts p kt ptag ctag v l a x hk hp hc
   index fuel history line rest target
 obtain ⟨hcopy⟩ := HistoryAppend.TableEquationsProof.consCopies p (outputConsTag st) ctag hout hc
   (entryValue et line) history
 obtain ⟨hinj⟩ := ConsInjectiveProof.consInjective p ctag hc (entryValue et line) history
   (HistoryKernel.pairCall ptag context raw) tail
 obtain ⟨hw⟩ := EntryWitnessProof.fromAcceptedEntry p itag et ptag leftTag rightTag v l a x
   hi he hp hl hr index fuel history line context raw
 have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have parts := Hilbert.Local.mp (.base hparts) e
 have accepted := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) parts
 have neweq := Hilbert.Local.mp (.base (.logical (.andRight _ _))) parts
 have consEq := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hcopy)) neweq
 have entryEq := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (.mp (.base hinj) consEq)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base hw) accepted) entryEq))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ActiveStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ActiveStepProof
