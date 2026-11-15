module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.EnvironmentProof
open GorbowSyntax
/-- Original de Bruijn ordering: bound variables occupy [0,depth), and the
one free variable is index depth. No term/formula encoding is changed. -/
def environment (depth : Nat) : FixedFormulaSubstitution.Environment (depth+1) depth 1 :=
 fun i => if h : i.val < depth then .inl ⟨i.val,h⟩ else .inr 0
theorem atZero : environment 0 = FullFormulaInstantiation.environment := by
 funext i
 simp [environment, FullFormulaInstantiation.environment]
/-- The exact capture-correct environment used by the original constructor
compiler agrees with increasing the pending original binder depth. -/
theorem lifted (depth : Nat) :
 FixedFormulaSubstitution.liftEnvironment (environment depth) = environment (depth+1) := by
 funext i
 cases i using Fin.cases with
 | zero => simp [FixedFormulaSubstitution.liftEnvironment, environment]
 | succ i =>
  by_cases h : i.val < depth
  · have hs : i.val + 1 < depth + 1 := Nat.succ_lt_succ h
    simp [FixedFormulaSubstitution.liftEnvironment, environment, h, hs]
  · have hs : ¬ i.val + 1 < depth + 1 := by omega
    simp [FixedFormulaSubstitution.liftEnvironment, environment, h, hs]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.EnvironmentProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.EnvironmentProof
