module

public import LogicLineages.ModelsAlgebra.Forests.Definitions
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin

/-! Paper 03 `prop:certificate`, semantic bounded-host component only.
Forests have their actual partial orders and predecessor-chain property;
embeddings are Mathlib order embeddings, with no root/meet requirements.
These bundles are mathematical objects, not an effective coding of inputs. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

structure FiniteOrderForest where
  Carrier : Type
  carrierFintype : Fintype Carrier
  carrierPartialOrder : PartialOrder Carrier
  forest : @IsOrderForest Carrier carrierPartialOrder

attribute [instance] FiniteOrderForest.carrierFintype FiniteOrderForest.carrierPartialOrder

/-- The actual finite forbidden-family avoidance condition. No hereditary
predicate or graph-representation theorem is supplied as an assumption. -/
def AvoidsForbidden (U : List FiniteOrderForest) (α : Type) [PartialOrder α] : Prop :=
  ∀ B ∈ U, ¬ Nonempty (B.Carrier ↪o α)

/-- The induced suborder on exactly the union of the two embedding images.
The two images may overlap; all three carriers may be empty. -/
abbrev JointImage {F G H : FiniteOrderForest}
    (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier) :=
  {x : H.Carrier // x ∈ Set.range f ∪ Set.range g}

noncomputable instance jointImageFintype {F G H : FiniteOrderForest}
    (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier) :
    Fintype (JointImage f g) := Fintype.ofFinite _

/-- Raw factoring functions; being order embeddings and composing back to
the original maps are independent proof targets. -/
def jointImageLeftFun {F G H : FiniteOrderForest}
    (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier)
    (x : F.Carrier) : JointImage f g := ⟨f x, Or.inl ⟨x, rfl⟩⟩

def jointImageRightFun {F G H : FiniteOrderForest}
    (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier)
    (x : G.Carrier) : JointImage f g := ⟨g x, Or.inr ⟨x, rfl⟩⟩

end LogicLineages.ModelsAlgebra.Forests
