module

public import LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleDefinitions

/-! Exact single-edge quotient for the unrestricted parent-label contraction
reading in Carter v1 introduction. This does not define general tree minors or
assert that this operation matches other possible repaired conventions. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CotreeCounterexample

def ParentLabelContraction {n m} (S : CotreeData n) (T : CotreeData m)
    (p c : Fin n) (f : Fin n → Fin m) : Prop :=
  child S p c ∧ Function.Surjective f ∧ f S.root = T.root ∧
  (∀ x y, f x = f y ↔ x = y ∨ (x = p ∧ y = c) ∨ (x = c ∧ y = p)) ∧
  (∀ x, x ≠ c → T.label (f x) = S.label x) ∧
  (∀ a b, child T a b ↔ a ≠ b ∧ ∃ x y, child S x y ∧ f x = a ∧ f y = b)

def contractionHost : CotreeData 5 where
  root := 0
  parent := fun x => if x.val ≤ 2 then 0 else 2
  label := fun x => if x = 0 then .union else if x = 2 then .join else .leaf

def contractionLeaves : Fin 3 → Fin 5 := ![1, 3, 4]

def contractionQuotient : Fin 5 → Fin 4 := ![0, 1, 0, 2, 3]

/-- Vertex 0 isolated, with the single edge between vertices 1 and 2. -/
def isolatedEdgeGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun i j => i = 1 ∧ j = 2)

end LogicLineages.ModelsAlgebra.Forests.CotreeCounterexample
