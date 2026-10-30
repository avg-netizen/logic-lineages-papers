module
public import LogicLineages.OrdinalComparison.WWTypedPartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- The literal same-context substitution X:=1, retaining all other names. -/
def ordinalHeadReplacementComponent {Γ : List Ty} {σ : Ty} :
    OrdinalComponent (σ :: Γ) → OrdinalExpression (σ :: Γ)
  | ⟨_, .here, _⟩ => .one
  | ⟨τ, .there v, i⟩ => .var ⟨τ, .there v, i⟩

def ordinalHeadReplacement {Γ : List Ty} {σ : Ty} :
    OrdinalExpression (σ :: Γ) → OrdinalExpression (σ :: Γ) :=
  substitute ordinalHeadReplacementComponent

abbrev OrdinalRawPartialVector (Γ : List Ty) (σ : Ty) :=
  Fin (σ.level + 2) → OrdinalExpression (σ :: Γ)

def ordinalPartialWeaken {Γ : List Ty} {σ : Ty} (v : OrdinalPartialVector Γ σ) :
    OrdinalRawPartialVector Γ σ := fun j => ordinalExpressionRename (Renaming.weaken Γ σ) (v j)

/-- Independent literal same-context WW partial. No call to the erased-context
partial occurs in this definition; equivalence is a separate theorem. -/
def ordinalRawPartial {Γ : List Ty} {σ : Ty} (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) : Option (OrdinalRawPartialVector Γ σ) :=
  if ordinalHeadFree t then some (fun j => if i = j.val then .add t .one else .one) else
  match t with
  | .var ⟨_, _, k⟩ => if i = k.val then some (fun _ => .one) else none
  | .zero | .one | .omega => none
  | .add f g => do
      let pf ← ordinalRawPartial i f
      let pg ← ordinalRawPartial i g
      pure fun j => .add (.add (pf j) (pg j)) .one
  | .emul f g => if 0 < i then do
      let pf ← ordinalRawPartial (i + 1) f
      let pg ← ordinalRawPartial i g
      pure fun j => .add (.add (.add (pf j) (pf j)) (pg j)) .one
    else none
  | .collapse f g => if i = 0 then do
      let pf ← ordinalRawPartial 1 f
      let pg ← ordinalRawPartial 0 g
      pure fun j => if j.val = 0 then .collapse (ordinalHeadReplacement f) (pg 0)
        else .add (pf j) (pg j)
    else none

end LogicLineages.OrdinalComparison.Source
