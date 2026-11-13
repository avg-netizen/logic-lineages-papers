module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepOptionsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport KeepSyntax

def optionTemplate {ctx : Nat} itag ptag ctag vtag leftTag rightTag
 (lines context raw tail remaining index fuel : Term ctx) : Formula (ctx+1) :=
 stateKeep itag ptag ctag vtag leftTag rightTag (.var 0) (liftTerm lines)
   (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)

theorem optionAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag
 (lines context raw tail remaining index fuel option : Term ctx) :
 GorbowStandardInstances.instantiate (optionTemplate itag ptag ctag vtag leftTag rightTag
   lines context raw tail remaining index fuel) option =
 stateKeep itag ptag ctag vtag leftTag rightTag option lines context raw tail remaining index fuel := by
 simp only [optionTemplate,GorbowStandardInstances.instantiate,substStateKeep,
   substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem allOptions {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (option line rest context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (stateKeep itag ptag ctag (validityTag itag v l a x) leftTag rightTag option
     (HistoryLookup.consCall ctag line rest) context raw tail remaining index fuel)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := optionTemplate itag ptag ctag (validityTag itag v l a x) leftTag rightTag
   (HistoryLookup.consCall ctag line rest) context raw tail remaining index fuel
 obtain ⟨hz⟩ := KeepCasesProof.noneConsCase p itag ptag ctag (validityTag itag v l a x) leftTag rightTag
   v l a x hi hp hc line rest context raw tail remaining index fuel
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
   simpa only [phi,optionAt] using hz
 obtain ⟨hs⟩ := KeepCasesProof.someConsCase p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   (.var (0 : Fin (ctx+1))) (liftTerm line) (liftTerm rest) (liftTerm context) (liftTerm raw)
   (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)
 have hs' : Derivation T (GorbowStandardInduction.successorInstance phi) := by
   simpa only [phi,optionTemplate,GorbowStandardInduction.successorInstance,substStateKeep,
     HistoryLookup.DropEquationsProof.substCons,substitute,successorLift,
     HistoryOrder.SupportProof.substituteLift,liftTerm,Fin.cases_zero] using hs
 have h := atTerm phi option (induction phi hb (Hilbert.lift phi hs'))
 simpa only [phi,optionAt] using (show Nonempty (Derivation T
   (GorbowStandardInstances.instantiate phi option)) from ⟨h⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepOptionsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepOptionsProof
