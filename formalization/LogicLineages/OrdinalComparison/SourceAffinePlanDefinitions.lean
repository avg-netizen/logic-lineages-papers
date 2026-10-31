module
public import LogicLineages.OrdinalComparison.SourceBinaryPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AffinePlan
open PrimitiveLowering ExistentialPlan

def addBind {Γ} (a b : Port Γ) (q : Plan (.ground::Γ)) : Plan Γ :=
  .existsGround (.gate (.add (portRename (Renaming.weaken Γ .ground) a)
    (portRename (Renaming.weaken Γ .ground) b) (.var .here)) q)

/-- Multiplication by a fixed syntactic natural coefficient, using only repeated addition. -/
def mulPlan {Γ} : Nat → Port Γ → Port Γ → Plan Γ → Plan Γ
  | 0,a,out,q => .gate (.eq out .zero) q
  | p+1,a,out,q => .existsGround
      (mulPlan p (portRename (Renaming.weaken Γ .ground) a) (.var .here)
        (.gate (.add (.var .here) (portRename (Renaming.weaken Γ .ground) a)
          (portRename (Renaming.weaken Γ .ground) out))
          (BinaryPlan.renamePlan (Renaming.weaken Γ .ground) q)))
def mulBind {Γ} (p : Nat) (a : Port Γ) (q : Plan (.ground::Γ)) : Plan Γ :=
  .existsGround (mulPlan p (portRename (Renaming.weaken Γ .ground) a) (.var .here) q)

/-- All intermediate values are shared ground wires; c uses the accepted binary literal plan. -/
def affinePlan {Γ} (p c : Nat) (a x y : Port Γ) : Plan Γ :=
  mulBind p a (addBind (.var .here) (portRename (Renaming.weaken Γ .ground) x)
    (BinaryPlan.constantPlan c
      (addBind (.var .here) (portRename (shift 3) y)
        (.gate (.eq (.var (.there (.there .here))) (.var .here)) .done))))
end LogicLineages.OrdinalComparison.Source.AffinePlan
