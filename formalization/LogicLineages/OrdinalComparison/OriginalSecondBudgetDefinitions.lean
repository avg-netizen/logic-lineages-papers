module
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalSecondBudget

/-- Literal scalar output-two count with the actual whole-free-first stop.
Outside the graded scalar-tree domain this is only a total syntax function. -/
def scalarSecond {Γ : List Ty} {σ : Ty} : OrdinalExpression (σ :: Γ) → Nat
  | .add a b => if ordinalHeadFree (.add a b) then 1 else scalarSecond a + scalarSecond b + 1
  | .collapse h t => if ordinalHeadFree (.collapse h t) then 1 else
      HeadFiniteSurplus.secondCount h + scalarSecond t
  | _ => 1

/-- The second field of the original functional abstraction/full box, not
of a truncated ground application result. -/
def boxSecond (k : Nat) : Fin ((Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level+1) :=
  ⟨2,by
    have h := (UnaryCarrier.headIndex k).isLt
    change 1 < (Ty.curriedGround (k+1)).level+1 at h
    change 2 < max ((Ty.curriedGround (k+1)).level+1) Ty.ground.level+1
    simp only [Ty.level]
    omega⟩
end LogicLineages.OrdinalComparison.Source.OriginalSecondBudget
