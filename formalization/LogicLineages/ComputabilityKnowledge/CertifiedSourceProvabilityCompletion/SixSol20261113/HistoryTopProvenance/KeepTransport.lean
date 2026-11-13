module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepTransport
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph KeepSyntax

theorem stateLinesAt {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (option lines context raw tail remaining index fuel : Term ctx) :
 GorbowStandardInstances.instantiate
   (stateKeep itag ptag ctag vtag leftTag rightTag (liftTerm option) (.var 0)
     (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)) lines =
 stateKeep itag ptag ctag vtag leftTag rightTag option lines context raw tail remaining index fuel := by
 simp only [GorbowStandardInstances.instantiate,substStateKeep,
   substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def lines {T : Sentence → Prop} {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (option a b context raw tail remaining index fuel : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp
   (stateKeep itag ptag ctag vtag leftTag rightTag option a context raw tail remaining index fuel)
   (stateKeep itag ptag ctag vtag leftTag rightTag option b context raw tail remaining index fuel))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
   (stateKeep itag ptag ctag vtag leftTag rightTag (liftTerm option) (.var 0)
     (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)) a b)
 simpa only [GorbowPACore.logicalFormula,stateLinesAt] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepTransport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepTransport
