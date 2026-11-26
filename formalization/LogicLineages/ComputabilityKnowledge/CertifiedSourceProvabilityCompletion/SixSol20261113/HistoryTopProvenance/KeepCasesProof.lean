module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepCasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport KeepSyntax

theorem nilCase {n ctx : Nat} (p : Program n) (itag ptag ctag vtag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (option context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (stateKeep itag ptag ctag vtag leftTag rightTag option .zero context raw tail remaining index fuel)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code := HistoryRunSplice.state ptag option .zero
 let target := HistoryRunSplice.state ptag (.succ (HistoryLookup.consCall ctag
   (HistoryKernel.pairCall ptag context raw) tail)) remaining
 let Q := topWitness vtag leftTag rightTag context raw
 let P := Formula.imp (.equal code target) Q
 let E := Formula.equal (HistoryKernel.kernelCall (kernelTag itag) code index fuel) target
 obtain ⟨hn⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNil p (kernelTag itag) ptag v l a x
   (HistoryRunSplice.IdleProof.kernelInstalled p itag v l a x hi) hp option index fuel
 have e : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have ih : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have eq := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hn)) e
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp ih eq)))⟩

theorem noneConsCase {n ctx : Nat} (p : Program n) (itag ptag ctag vtag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (line rest context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (stateKeep itag ptag ctag vtag leftTag rightTag .zero
     (HistoryLookup.consCall ctag line rest) context raw tail remaining index fuel)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code := HistoryRunSplice.state ptag .zero (HistoryLookup.consCall ctag line rest)
 let out := HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail
 let target := HistoryRunSplice.state ptag (.succ out) remaining
 let Q := topWitness vtag leftTag rightTag context raw
 let P := Formula.imp (.equal code target) Q
 let E := Formula.equal (HistoryKernel.kernelCall (kernelTag itag) code index fuel) target
 obtain ⟨hn⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNoneCons p (kernelTag itag) ptag ctag v l a x
   (HistoryRunSplice.IdleProof.kernelInstalled p itag v l a x hi) hp hc line rest index fuel
 obtain ⟨hinj⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx .zero rest (.succ out) remaining
 have e : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have eq := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hn)) e
 have pieces := Hilbert.Local.mp (.base hinj) eq
 have bad := HistoryOrder.StepProof.localSym _ _ (Hilbert.Local.mp (.base (.logical (.andLeft _ _))) pieces)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
   (Hilbert.Local.explosion Q bad (.base (.arithmetic (.succNotZero out))))))⟩

theorem someConsCase {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (history line rest context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (stateKeep itag ptag ctag (validityTag itag v l a x) leftTag rightTag (.succ history)
     (HistoryLookup.consCall ctag line rest) context raw tail remaining index fuel)) := by
 obtain ⟨h⟩ := OutputRestProof.activeStepAnyRemaining p itag ptag ctag leftTag rightTag v l a x
   hi hp hc hl hr history line rest index fuel context raw tail remaining
 exact ⟨Hilbert.lift _ h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepCasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepCasesProof
