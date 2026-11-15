module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TransportProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph InvariantProof
noncomputable def oldTasks {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r
 (tokens raw a b newTasks rest out : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (property ftag stag ptag ctag atag len q l r tokens raw a newTasks rest out)
   (property ftag stag ptag ctag atag len q l r tokens raw b newTasks rest out))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (property ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (.var 0) (liftTerm newTasks) (liftTerm rest) (liftTerm out)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def newTasks {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r
 (tokens raw oldTasks a b rest out : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (property ftag stag ptag ctag atag len q l r tokens raw oldTasks a rest out)
   (property ftag stag ptag ctag atag len q l r tokens raw oldTasks b rest out))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (property ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (liftTerm oldTasks) (.var 0) (liftTerm rest) (liftTerm out)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TransportProof
