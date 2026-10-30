module
public import LogicLineages.OrdinalComparison.WWTypedComponentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ordinalHeadComponentOccurs {Γ : List Ty} {σ : Ty} : OrdinalComponent (σ :: Γ) → Bool
  | ⟨_, .here, _⟩ => true
  | ⟨_, .there _, _⟩ => false

def ordinalHeadOccurs {Γ : List Ty} {σ : Ty} : OrdinalExpression (σ :: Γ) → Bool
  | .var c => ordinalHeadComponentOccurs c
  | .zero | .one | .omega => false
  | .add f g | .emul f g | .collapse f g => ordinalHeadOccurs f || ordinalHeadOccurs g

def ordinalHeadFree {Γ : List Ty} {σ : Ty} (t : OrdinalExpression (σ :: Γ)) : Bool :=
  !ordinalHeadOccurs t

/-- WW's whole-free-first syntactic size; no semantic simplification of trees. -/
def ordinalPartialSize {Γ : List Ty} {σ : Ty} (t : OrdinalExpression (σ :: Γ)) : Nat :=
  if ordinalHeadFree t then 1 else
  match t with
  | .var _ | .zero | .one | .omega => 1
  | .add f g | .collapse f g => ordinalPartialSize f + ordinalPartialSize g + 1
  | .emul f g => 2 * ordinalPartialSize f + ordinalPartialSize g + 1

abbrev OrdinalPartialVector (Γ : List Ty) (σ : Ty) :=
  Fin (σ.level + 2) → OrdinalExpression Γ

def ordinalFreePartialVector {Γ : List Ty} {σ : Ty} (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) : OrdinalPartialVector Γ σ :=
  fun j => if i = j.val then .add (ordinalHeadClosure t) .one else .one

/-- Literal syntactic partial, with invalid active shapes rejected explicitly.
The whole-free case has priority over every constructor/index check. Returning
old-context trees records elimination of X, not an assumed source-domain theorem. -/
def ordinalTypedPartial {Γ : List Ty} {σ : Ty} (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) : Option (OrdinalPartialVector Γ σ) :=
  if ordinalHeadFree t then some (ordinalFreePartialVector i t) else
  match t with
  | .var ⟨_, _, k⟩ => if i = k.val then some (fun _ => .one) else none
  | .zero | .one | .omega => none
  | .add f g => do
      let pf ← ordinalTypedPartial i f
      let pg ← ordinalTypedPartial i g
      pure fun j => .add (.add (pf j) (pg j)) .one
  | .emul f g => if 0 < i then do
      let pf ← ordinalTypedPartial (i + 1) f
      let pg ← ordinalTypedPartial i g
      pure fun j => .add (.add (.add (pf j) (pf j)) (pg j)) .one
    else none
  | .collapse f g => if i = 0 then do
      let pf ← ordinalTypedPartial 1 f
      let pg ← ordinalTypedPartial 0 g
      pure fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
        else .add (pf j) (pg j)
    else none

end LogicLineages.OrdinalComparison.Source
