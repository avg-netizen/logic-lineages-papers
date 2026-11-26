module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.PositiveLinesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepLinesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport KeepSyntax

def linesTemplate {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (option context raw tail remaining index fuel : Term ctx) : Formula (ctx+1) :=
 stateKeep itag ptag ctag vtag leftTag rightTag (liftTerm option) (.var 0)
   (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)

theorem linesAt {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (option context raw tail remaining index fuel lines : Term ctx) :
 GorbowStandardInstances.instantiate (linesTemplate itag ptag ctag vtag leftTag rightTag
   option context raw tail remaining index fuel) lines =
 stateKeep itag ptag ctag vtag leftTag rightTag option lines context raw tail remaining index fuel := by
 simp only [linesTemplate,GorbowStandardInstances.instantiate,substStateKeep,
   substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem allLines {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (option lines context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (stateKeep itag ptag ctag (validityTag itag v l a x) leftTag rightTag option
     lines context raw tail remaining index fuel)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := linesTemplate itag ptag ctag (validityTag itag v l a x) leftTag rightTag
   option context raw tail remaining index fuel
 obtain ⟨hz⟩ := KeepCasesProof.nilCase p itag ptag ctag (validityTag itag v l a x) leftTag rightTag
   v l a x hi hp option context raw tail remaining index fuel
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
   simpa only [phi,linesAt] using hz
 obtain ⟨hs⟩ := PositiveLinesProof.positiveLines p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   (liftTerm option) (.var (0 : Fin (ctx+1))) (liftTerm context) (liftTerm raw)
   (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)
 have hs' : Derivation T (GorbowStandardInduction.successorInstance phi) := by
   simpa only [phi,linesTemplate,GorbowStandardInduction.successorInstance,substStateKeep,
     KeepSuccessorSyntax.liftAtSuccessor,substitute,Fin.cases_zero] using hs
 have h := atTerm phi lines (induction phi hb (Hilbert.lift phi hs'))
 simpa only [phi,linesAt] using (show Nonempty (Derivation T
   (GorbowStandardInstances.instantiate phi lines)) from ⟨h⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepLinesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepLinesProof
