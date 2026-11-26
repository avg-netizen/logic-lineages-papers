module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.EnvironmentProof
open GorbowSyntax FixedFormulaSubstitution List.Vector
/-- Both original binders commute with removal of the last protected index.
The inserted bound variable0 stays bound; runtime closed coordinates never shift internally. -/
theorem lifted {n depth inputs : Nat} (e : Environment n (depth+1) inputs) :
 specialize (liftEnvironment e) = liftEnvironment (specialize e) := by
 funext i
 cases i using Fin.cases with
 | zero => simp [specialize,liftEnvironment]
 | succ i =>
  cases he : e i with
  | inl j =>
   by_cases h : j.val < depth
   · have hs : j.val + 1 < depth + 1 := Nat.succ_lt_succ h
     simp [specialize,liftEnvironment,he,h,hs]
   · have hs : ¬ j.val + 1 < depth + 1 := by omega
     simp [specialize,liftEnvironment,he,h,hs]
  | inr j => simp [specialize,liftEnvironment,he]
/-- Existing closed runtime chunk is preserved verbatim in the new vector. -/
theorem runtimeValue {n depth inputs ctx : Nat} (ctag atag : Nat)
 (e : Environment n (depth+1) inputs) (raw : List.Vector (Term ctx) inputs)
 (replacement : Term ctx) (i : Fin n) (j : Fin inputs) (h : e i = .inr j) :
 termValue ctag atag (specialize e) (replacement ::ᵥ raw) (.var i) = raw.get j := by
 simp [termValue,specialize,h]
/-- A bound-coordinate substitution is the exact previously checked original
variable traversal at depth, not a reinterpretation of a dynamic formula. -/
theorem boundValue {n depth inputs ctx : Nat} (ctag atag : Nat)
 (e : Environment n (depth+1) inputs) (raw : List.Vector (Term ctx) inputs)
 (replacement : Term ctx) (i : Fin n) (j : Fin (depth+1)) (h : e i = .inl j) :
 termValue ctag atag (specialize e) (replacement ::ᵥ raw) (.var i) =
 termValue ctag atag (UniformFixedFormulaAgreement.EnvironmentProof.environment depth)
  (replacement ::ᵥ nil) (.var j) := by
 by_cases hj : j.val < depth
 · simp [termValue,specialize,h,UniformFixedFormulaAgreement.EnvironmentProof.environment,hj]
 · simp [termValue,specialize,h,UniformFixedFormulaAgreement.EnvironmentProof.environment,hj]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.EnvironmentProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.EnvironmentProof
