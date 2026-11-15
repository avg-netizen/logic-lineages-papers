module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.TraceSupportProof
open GorbowSyntax GorbowFormulaSubstitution FixedFormulaSubstitution List.Vector
theorem assignmentRuntime {n : Nat} (sigma : Fin n → Term 0) :
 assignment (runtimeEnvironment n) sigma = sigma := by
 funext i
 change renameTerm (Fin.elim0 : Fin 0 → Fin 0) (sigma i) = sigma i
 unfold renameTerm
 have he : (fun j : Fin 0 => Term.var (Fin.elim0 j)) = Term.var := by
  funext j
  exact Fin.elim0 j
 rw [he]
 exact GorbowSubstitution.substitute_variables (sigma i)
theorem assignmentHead {n : Nat} (sigma : Fin n → Term 0) :
 assignment (headEnvironment n) sigma = liftSubstitute sigma := by
 rw [← EnvironmentProof.liftRuntime,FixedFormulaSubstitution.NativeProof.assignmentLift,assignmentRuntime]
theorem tailInputs {n ctx : Nat} (sigma : Fin (n+1) → Term 0) :
 (numeralInputs (ctx := ctx) sigma).tail = numeralInputs (fun i => sigma i.succ) := by
 exact List.Vector.tail_ofFn _
theorem headInputs {n ctx : Nat} (sigma : Fin (n+1) → Term 0) :
 (numeralInputs (ctx := ctx) sigma).head = Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (sigma 0))) := by
 exact List.Vector.head_ofFn _
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.TraceSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.TraceSupportProof
