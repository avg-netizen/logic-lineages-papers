module
public import LogicLineages.OrdinalComparison.DeterministicAccountDataDefinitions
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListDefinitions
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalGroundDataConstruction
open DeterministicAccountData

/-- Proof-only wrapping preserves the given raw bytes and shared old context.
The two tracked slots are private; Γ is the single shared base. -/
def operators {k Γ}
    (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
    (ha : ∀ r ∈ rs, r.Assigned) : List (HeterogeneousUnaryAssembly.Operator Γ) :=
  rs.attach.map (fun r =>
    ({ privateContext := [Ty.curriedGround (k+1),Ty.curriedGround (k+1)]
       term := r.val.source
       vector := r.val.vector
       assigned := by exact ha r.val r.property } : HeterogeneousUnaryAssembly.Operator Γ))

def boxFirst (k : Nat) : Fin ((Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level+1) :=
  ⟨1,by have := (OriginalSecondBudget.boxSecond k).isLt;change 2 < _ at this;omega⟩
end LogicLineages.OrdinalComparison.Source.OriginalGroundDataConstruction
