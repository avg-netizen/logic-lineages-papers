module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ActiveStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.OutputRestProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel.TransitionEquationsProof

/-- A successful active transition has the consumed tail as remaining input.
No preservation of an unrelated output field is assumed. -/
theorem restEquality {n ctx : Nat} (p : Program n) (ktag ptag ctag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hk : (nodes p)[ktag]? = some ⟨3,HistoryKernel.kernel v l a x⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (history line rest index fuel out remaining : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (.equal (HistoryKernel.kernelCall ktag
     (HistoryKernel.activeState ptag ctag history line rest) index fuel)
     (HistoryKernel.pairCall ptag out remaining)) (.equal remaining rest))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := Formula.equal (HistoryKernel.kernelCall ktag
     (HistoryKernel.activeState ptag ctag history line rest) index fuel)
     (HistoryKernel.pairCall ptag out remaining)
 obtain ⟨hn⟩ := HistoryRunSplice.FirstStepProof.someKernel p ktag ptag ctag v l a x hk hp hc
   history line rest index fuel
 obtain ⟨hinj⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx
   (optionValue ktag v l a x index fuel history line) rest out remaining
 have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have ep := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hn)) e
 have er := Hilbert.Local.mp (.base (.logical (.andRight _ _))) (.mp (.base hinj) ep)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (HistoryOrder.StepProof.localSym _ _ er))⟩

theorem activeStepAnyRemaining {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (history line rest index fuel context raw tail remaining : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (.equal (HistoryKernel.kernelCall (kernelTag itag)
     (HistoryKernel.activeState ptag ctag history line rest) index fuel)
     (HistoryKernel.pairCall ptag (.succ (HistoryLookup.consCall ctag
       (HistoryKernel.pairCall ptag context raw) tail)) remaining))
     (topWitness (validityTag itag v l a x) leftTag rightTag context raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let out := Term.succ (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail)
 let E := Formula.equal (HistoryKernel.kernelCall (kernelTag itag)
     (HistoryKernel.activeState ptag ctag history line rest) index fuel)
     (HistoryKernel.pairCall ptag out remaining)
 obtain ⟨hrest⟩ := restEquality p (kernelTag itag) ptag ctag v l a x
   (HistoryRunSplice.IdleProof.kernelInstalled p itag v l a x hi) hp hc
   history line rest index fuel out remaining
 obtain ⟨ha⟩ := ActiveStepProof.activeStep p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   history line rest index fuel context raw tail
 have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have r := Hilbert.Local.mp (.base hrest) e
 have pairEq := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag out remaining out rest
   (Hilbert.Local.base (.logical (.reflexive out))) r
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
   (.mp (.base ha) (localTrans _ _ _ e pairEq)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.OutputRestProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.OutputRestProof
