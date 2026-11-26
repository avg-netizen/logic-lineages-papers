module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSuccessorSyntax
open GorbowSyntax GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel

theorem liftAtSuccessor {ctx : Nat} (t : Term ctx) :
 substitute (Fin.cases (.succ (.var 0)) (fun i : Fin ctx => Term.var i.succ)) (liftTerm t) =
 liftTerm t := by
 unfold liftTerm renameTerm
 rw [substitute_composition]
 have he : (fun i : Fin ctx => substitute
   (Fin.cases (.succ (.var 0)) (fun j : Fin ctx => Term.var j.succ)) (Term.var i.succ)) =
   (fun i : Fin ctx => Term.var i.succ) := by
   funext i
   rfl
 rw [he]

theorem liftCons {ctx : Nat} ctag (a b : Term ctx) :
 liftTerm (HistoryLookup.consCall ctag a b) =
 HistoryLookup.consCall ctag (liftTerm a) (liftTerm b) := by
 simp only [liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSuccessorSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSuccessorSyntax
