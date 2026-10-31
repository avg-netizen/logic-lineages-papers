module
public import LogicLineages.OrdinalComparison.SourceExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BinaryPlan
open GroundEquivalence PrimitiveLowering ExistentialPlan SourceAdditionCompletion

/-- Rename every actual source DAG and primitive port in one pass, lifting
under each existential binder. No tail or supplied source is duplicated. -/
def renamePlan {Γ Δ : List Ty} (r : Renaming Γ Δ) : Plan Γ → Plan Δ
  | .done => .done
  | .equation a b q => .equation (ScopedDAG.renameInput r a) (ScopedDAG.renameInput r b) (renamePlan r q)
  | .gate g q => .gate (gateRename r g) (renamePlan r q)
  | .existsGround q => .existsGround (renamePlan (Renaming.lift r) q)

/-- Concrete continuation-passing lowering of the existing shared binary
literal DAG. Its single predecessor and its continuation each occur once. -/
def binaryPlan {Γ : List Ty} : BinaryDAG → Port Γ → Plan Γ → Plan Γ
  | .zero, out, q => .gate (.eq out .zero) q
  | .one, out, q => .gate (.one out) q
  | .double p, out, q =>
      .existsGround (binaryPlan p (.var .here)
        (.gate (.add (.var .here) (.var .here) (portRename (Renaming.weaken Γ .ground) out))
          (renamePlan (Renaming.weaken Γ .ground) q)))
  | .doubleOne p, out, q =>
      .existsGround (.existsGround (.existsGround
        (binaryPlan p (.var (.there (.there .here)))
          (.gate (.add (.var (.there (.there .here))) (.var (.there (.there .here))) (.var (.there .here)))
            (.gate (.one (.var .here))
              (.gate (.add (.var (.there .here)) (.var .here) (portRename (shift 3) out))
                (renamePlan (shift 3) q)))))))

/-- Bind the literal value itself as one fresh ground wire and retain q once. -/
def constantPlan {Γ : List Ty} (k : Nat) (q : Plan (.ground::Γ)) : Plan Γ :=
  .existsGround (binaryPlan (binaryDAG k) (.var .here) q)
end LogicLineages.OrdinalComparison.Source.BinaryPlan
