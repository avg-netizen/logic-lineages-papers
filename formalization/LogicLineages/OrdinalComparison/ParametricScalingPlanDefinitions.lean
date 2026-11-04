module
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricScalingPlan
open PrimitiveLowering ExistentialPlan BinaryPlan
/-- One shared intermediate wire per doubling, with the continuation retained once. -/
def scalePlan {Γ : List Ty} : Nat → Port Γ → Port Γ → Plan Γ → Plan Γ
  | 0, a, out, q => .gate (.eq a out) q
  | e+1, a, out, q => .existsGround
      (scalePlan e (portRename (Renaming.weaken Γ .ground) a) (.var .here)
        (.gate (.add (.var .here) (.var .here) (portRename (Renaming.weaken Γ .ground) out))
          (renamePlan (Renaming.weaken Γ .ground) q)))
end LogicLineages.OrdinalComparison.Source.ParametricScalingPlan
