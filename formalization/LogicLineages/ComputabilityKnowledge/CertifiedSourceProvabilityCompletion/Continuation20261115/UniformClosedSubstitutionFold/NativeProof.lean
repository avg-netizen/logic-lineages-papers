module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.NativeStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.NativeProof
open GorbowPRProgram List.Vector NativeStepProof
theorem iteratorZero (s raw : Nat) : evaluate iterator (0 ::ᵥ s ::ᵥ raw ::ᵥ nil) = s := rfl
theorem iteratorSucc (count s raw : Nat) : evaluate iterator (count.succ ::ᵥ s ::ᵥ raw ::ᵥ nil) =
 evaluate tick (evaluate iterator (count ::ᵥ s ::ᵥ raw ::ᵥ nil) ::ᵥ raw ::ᵥ nil) := rfl
theorem iteratorFirst (count s raw : Nat) : evaluate iterator (count.succ ::ᵥ s ::ᵥ raw ::ᵥ nil) =
 evaluate iterator (count ::ᵥ evaluate tick (s ::ᵥ raw ::ᵥ nil) ::ᵥ raw ::ᵥ nil) := by
 induction count generalizing s with
 | zero => rfl
 | succ count ih => rw [iteratorSucc,ih,iteratorSucc]
theorem exactOriginalFold : Targets.ExactOriginalFold := by
 intro s tokens raw hr
 induction tokens generalizing s with
 | nil => rfl
 | cons token tokens ih =>
  rw [List.length_cons,iteratorFirst,tickCons token tokens s raw hr,ih]
  rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.NativeProof
