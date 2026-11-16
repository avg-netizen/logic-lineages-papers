module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeUnary
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem renamed (t : Term 0) : GorbowFormulaSubstitution.renameTerm (Fin.elim0 : Fin 0 → Fin 0) t = t :=
 congrFun (PrescribedRuntimeSpecialization.TraceSupportProof.assignmentRuntime (fun _ : Fin 1 => t)) 0

theorem renamedLift (t : Term 0) : GorbowFormulaSubstitution.renameTerm (Fin.elim0 : Fin 0 → Fin 1) t =
 GorbowClosedEquality.liftClosedTerm 1 t := by
 unfold GorbowFormulaSubstitution.renameTerm GorbowClosedEquality.liftClosedTerm
 congr 1
 funext i
 exact Fin.elim0 i

theorem openBinary (multiply right : Bool) (t : Term 0) :
 GorbowSubstitution.substitute (FixedFormulaSubstitution.assignment binaryEnvironment (fun _ : Fin 1 => t))
  (if right then binaryTerm multiply (.var 1) (.var 0) else binaryTerm multiply (.var 0) (.var 1)) =
 (if right then binaryTerm multiply (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)
  else binaryTerm multiply (.var 0) (GorbowClosedEquality.liftClosedTerm 1 t)) := by
 cases right <;> cases multiply <;>
  simp only [binaryTerm,GorbowSubstitution.substitute,FixedFormulaSubstitution.assignment,binaryEnvironment,
   Fin.cases_zero,Fin.cases_succ,renamedLift]

theorem closedBinary (multiply right : Bool) (a b : Term 0) :
 GorbowSubstitution.substitute (FixedFormulaSubstitution.assignment (UniformRuntimeEnvironmentAgreement.specialize binaryEnvironment)
  (Fin.cases a (fun _ : Fin 1 => b)))
  (if right then binaryTerm multiply (.var 1) (.var 0) else binaryTerm multiply (.var 0) (.var 1)) =
 (if right then binaryTerm multiply b a else binaryTerm multiply a b) := by
 cases right <;> cases multiply <;>
  simp [binaryTerm,GorbowSubstitution.substitute,FixedFormulaSubstitution.assignment,binaryEnvironment,
   UniformRuntimeEnvironmentAgreement.specialize,renamed]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeSyntax
