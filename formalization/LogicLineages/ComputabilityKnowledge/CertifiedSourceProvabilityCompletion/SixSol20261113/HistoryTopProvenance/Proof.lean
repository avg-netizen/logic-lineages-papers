module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.CountStepProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.BaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def countTemplate {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (lines context raw tail remaining index fuel : Term ctx) : Formula (ctx+1) :=
 provenance itag ptag ctag vtag leftTag rightTag (.var 0) (liftTerm lines)
   (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)

theorem countAt {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
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
 obtain ⟨hs⟩ := CountStepProof.successor p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   (.var (0 : Fin (ctx+1))) (liftTerm lines) (liftTerm context) (liftTerm raw)
   (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)
 have hs' : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
   simpa only [phi,countTemplate,GorbowStandardInduction.successorInstance,SyntaxProof.substProvenance,
     KeepSuccessorSyntax.liftAtSuccessor,substitute,Fin.cases_zero] using hs
 have h := atTerm phi count (induction phi hb hs')
 simpa only [phi,countAt] using (show Nonempty (Derivation T
   (GorbowStandardInstances.instantiate phi count)) from ⟨h⟩)

theorem internalFullRunProvenance : Targets.InternalFullRunProvenance := by
 intro v l a x n p itag ptag ctag leftTag rightTag hi hp hc hl hr ctx lines context raw tail index fuel
 exact internalTopProvenance v l a x n p itag ptag ctag leftTag rightTag hi hp hc hl hr
   ctx lines lines context raw tail .zero index fuel
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Proof
