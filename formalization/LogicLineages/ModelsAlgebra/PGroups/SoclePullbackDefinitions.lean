module
public import LogicLineages.ModelsAlgebra.PGroups.CofinalSocleMapTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
variable {B C E:Type} [AddCommGroup B] [AddCommGroup C] [AddCommGroup E]
/-- The actual algebraic pullback of two actual additive homomorphisms. -/
def HomPullback (f:B→+C) (q:E→+C) : AddSubgroup (B×E) where
  carrier := {x|f x.1=q x.2}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy;simp only [Set.mem_setOf_eq] at *;simp only [map_add,Prod.fst_add,Prod.snd_add,hx,hy]
  neg_mem' := by intro x hx;simp only [Set.mem_setOf_eq] at *;simp only [map_neg,Prod.fst_neg,Prod.snd_neg,hx]
/-- Projection from the literal subgroup of the product. -/
def pullbackProjection (f:B→+C) (q:E→+C) : HomPullback f q→+B :=
  (AddMonoidHom.fst B E).comp (HomPullback f q).subtype
end LogicLineages.ModelsAlgebra.PGroups
