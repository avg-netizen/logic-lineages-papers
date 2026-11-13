module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.BaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.CountStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem successor {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (count lines context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (provenance itag ptag ctag (validityTag itag v l a x) leftTag rightTag
      count lines context raw tail remaining index fuel)
     (provenance itag ptag ctag (validityTag itag v l a x) leftTag rightTag
      (.succ count) lines context raw tail remaining index fuel))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let R := HistoryRunSplice.run itag ptag count (.succ .zero) lines index fuel
 let target := HistoryRunSplice.state ptag (.succ (HistoryLookup.consCall ctag
   (HistoryKernel.pairCall ptag context raw) tail)) remaining
 let Q := topWitness (validityTag itag v l a x) leftTag rightTag context raw
 let P := Formula.imp (.equal R target) Q
 let E := Formula.equal (HistoryRunSplice.run itag ptag (.succ count) (.succ .zero) lines index fuel) target
 obtain ⟨hk⟩ := KeepProof.everyState p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   R context raw tail remaining index fuel
 obtain ⟨hs⟩ := SixSol20261113.HistoryMachine.Equations.successor p itag (HistoryKernel.kernel v l a x) hi
   count (HistoryRunSplice.state ptag (.succ .zero) lines) index fuel
 have ih : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have e : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have he := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hs)) e
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.mp (.base hk) ih) he)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.CountStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.CountStepProof
