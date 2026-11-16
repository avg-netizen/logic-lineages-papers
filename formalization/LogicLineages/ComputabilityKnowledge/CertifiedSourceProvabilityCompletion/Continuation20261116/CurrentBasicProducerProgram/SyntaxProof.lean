module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SyntaxProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution PrescribedRuntimeEquality
theorem arguments (n target : Nat) :
 (List.Vector.ofFn (fun i : Fin n => (Term.var i.castSucc : Term (n+1)))).map
  (substitute (CurrentRecursionBaseProgram.TagSyntax.plug n target)) = argumentVariables n := by
 ext i
 simp only [List.Vector.get_map,List.Vector.get_ofFn,substitute,CurrentRecursionBaseProgram.TagSyntax.plugCast,argumentVariables]

theorem root {n : Nat} (kind : Kind n) (target : Nat) :
 substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug n target) (rootTemplate kind) = rootFormula kind target := by
 simp only [rootTemplate,substituteFormula,CurrentRecursionStepProgram.TemplateSyntax.openCallSubstitute,
  substitute,CurrentRecursionBaseProgram.TagSyntax.plugLast,arguments,rootFormula]
 have hcall : CurrentRecursionBaseProgram.openCall (Term.numeral (n := n) target) (argumentVariables n) =
  call target (argumentVariables n) := rfl
 rw [hcall]
 congr 1
 cases kind with
 | zero => rfl
 | successor =>
  simp only [rhs,renameTerm,substitute,CurrentRecursionBaseProgram.TagSyntax.plugCast]
 | projection i =>
  simp only [rhs,renameTerm,substitute,CurrentRecursionBaseProgram.TagSyntax.plugCast]

theorem equation {n : Nat} (kind : Kind n) (target : Nat) :
 GorbowStandardInduction.universalClosure (rootFormula kind target) ∈ nodeEquations (evaluator kind) target := by
 cases kind <;> exact List.mem_singleton.mpr rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SyntaxProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SyntaxProof
