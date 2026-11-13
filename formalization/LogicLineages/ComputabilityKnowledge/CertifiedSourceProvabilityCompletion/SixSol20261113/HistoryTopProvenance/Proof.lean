module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.BaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Proof
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

def countTemplate {ctx : Nat} itag ptag ctag vtag leftTag rightTag
 (lines context raw tail remaining index fuel : Term ctx) : Formula (ctx+1) :=
 provenance itag ptag ctag vtag leftTag rightTag (.var 0) (liftTerm lines)
   (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)

theorem countAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag
 (lines context raw tail remaining index fuel count : Term ctx) :
 GorbowStandardInstances.instantiate (countTemplate itag ptag ctag vtag leftTag rightTag
   lines context raw tail remaining index fuel) count =
 provenance itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index fuel := by
 simp only [countTemplate,GorbowStandardInstances.instantiate,SyntaxProof.substProvenance,
   substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem internalTopProvenance : Targets.InternalTopProvenance := by
 intro v l a x n p itag ptag ctag leftTag rightTag hi hp hc hl hr ctx count lines context raw tail remaining index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := countTemplate itag ptag ctag (validityTag itag v l a x) leftTag rightTag
   lines context raw tail remaining index fuel
 obtain ⟨hz⟩ := BaseProof.zeroCount p itag ptag ctag (validityTag itag v l a x) leftTag rightTag
   v l a x hi hp hc lines context raw tail remaining index fuel
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
   simpa only [phi,countAt] using hz
 obtain ⟨hs⟩ := successor p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   (.var (0 : Fin (ctx+1))) (liftTerm lines) (liftTerm context) (liftTerm raw)
   (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)
 have hs' : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
   simpa only [phi,countTemplate,GorbowStandardInduction.successorInstance,SyntaxProof.substProvenance,
     substitute,successorLift,HistoryOrder.SupportProof.substituteLift,liftTerm,Fin.cases_zero] using hs
 have h := atTerm phi count (induction phi hb hs')
 simpa only [phi,countAt] using (show Nonempty (Derivation T
   (GorbowStandardInstances.instantiate phi count)) from ⟨h⟩)

theorem internalFullRunProvenance : Targets.InternalFullRunProvenance := by
 intro v l a x n p itag ptag ctag leftTag rightTag hi hp hc hl hr ctx lines context raw tail index fuel
 exact internalTopProvenance v l a x n p itag ptag ctag leftTag rightTag hi hp hc hl hr
   ctx lines lines context raw tail .zero index fuel
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Proof
