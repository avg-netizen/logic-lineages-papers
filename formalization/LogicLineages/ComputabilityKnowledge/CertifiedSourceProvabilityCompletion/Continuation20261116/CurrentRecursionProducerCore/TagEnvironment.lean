module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagPlug
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagEnvironment
open GorbowSyntax GorbowSubstitution GorbowFormulaSubstitution GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open TagPlug

theorem lift {n depth inputs : Nat} (e : Environment n depth inputs) :
 liftEnvironment (tagEnvironment e) = tagEnvironment (liftEnvironment e) := by
 funext i
 cases i using Fin.cases with
 | zero =>
  change Sum.inl (0 : Fin (depth+1)) = tagEnvironment (liftEnvironment e) ((0 : Fin (n+1)).castSucc)
  simp only [tagEnvironment,Fin.lastCases_castSucc,liftEnvironment,Fin.cases_zero]
 | succ i =>
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hi : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
    conv_rhs => rw [hi]
    simp only [liftEnvironment,Fin.cases_succ,tagEnvironment,Fin.lastCases_last]
  · have hi : j.castSucc.succ = j.succ.castSucc := by apply Fin.ext; rfl
    conv_rhs => rw [hi]
    simp only [liftEnvironment,Fin.cases_succ,tagEnvironment,Fin.lastCases_castSucc]
    cases e j <;> rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagEnvironment
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagEnvironment
