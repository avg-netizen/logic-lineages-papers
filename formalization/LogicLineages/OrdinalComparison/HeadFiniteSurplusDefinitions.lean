module
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeDefinitions
public import LogicLineages.OrdinalComparison.WWUnitObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus

/-- Literal whole-free-first finite surplus. Outside additive head trees this
is only a total syntax function, not a claimed semantic invariant. -/
def surplus {Γ : List Ty} {σ : Ty} : OrdinalExpression (σ :: Γ) → Nat
  | .add a b => if ordinalHeadFree (.add a b) then 1 else surplus a + surplus b + 1
  | t => if ordinalHeadFree t then 1 else 0

/-- Exact finite value of output two on the admitted head tree. A whole-free
sum is one stop; it is not recursively counted as an active sum. -/
def secondCount {Γ : List Ty} {σ : Ty} : OrdinalExpression (σ :: Γ) → Nat
  | .add a b => if ordinalHeadFree (.add a b) then 1 else secondCount a + secondCount b + 1
  | _ => 1

def outputOne (k : Nat) : Fin ((Ty.curriedGround (k+1)).level+2) :=
  ⟨1,by have := (UnaryCarrier.headIndex k).isLt; change 1 < (Ty.curriedGround (k+1)).level+1 at this;omega⟩

def outputTwo (k : Nat) : Fin ((Ty.curriedGround (k+1)).level+2) :=
  ⟨2,by have := (UnaryCarrier.headIndex k).isLt; change 1 < (Ty.curriedGround (k+1)).level+1 at this;omega⟩
end LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus
