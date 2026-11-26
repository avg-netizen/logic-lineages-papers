module
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgramSizeTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open BooleanCompiler ExistentialPlan
/-- Every supplied table occurrence is paid, not assumed freely shared in the output. -/
def CopiedLoad : Prop := ∀ (Γ : List Ty) (q : Program Γ),
  q.load ≤ q.codeSize * (q.sourceMax + 1)
/-- Literal lowered Plan counts include real table lengths and primitive witnesses. -/
def LowerCounts : Prop := ∀ (Γ : List Ty) (q : Program Γ),
  (lower q).vertices ≤ 1000*q.load ∧
  (lower q).equations ≤ 1000*q.load ∧
  (lower q).witnesses ≤ 1000*q.load
/-- Actual sum of all table sizes in the compiled forest, equation count and context. -/
def ForestLoadCounts : Prop := ∀ (Γ : List Ty) (q : Program Γ),
  (compile (lower q)).nodes ≤ 1000*q.load ∧
  (compile (lower q)).forest.length ≤ 1000*q.load ∧
  (compile (lower q)).context.length ≤ Γ.length + 1000*q.load
/-- Same real output measures bounded by the syntactic code/table budget, not bit length. -/
def ForestCodeCounts : Prop := ∀ (Γ : List Ty) (q : Program Γ),
  (compile (lower q)).nodes ≤ 1000*q.codeSize*(q.sourceMax+1) ∧
  (compile (lower q)).forest.length ≤ 1000*q.codeSize*(q.sourceMax+1) ∧
  (compile (lower q)).context.length ≤ Γ.length + 1000*q.codeSize*(q.sourceMax+1)
end LogicLineages.ControlSensitivityCurrent.PolicyProgramSizeTargets
