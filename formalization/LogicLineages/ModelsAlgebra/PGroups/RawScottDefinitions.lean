module
public import LogicLineages.ModelsAlgebra.PGroups.RawGuardDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

structure RawIsomorphism {G H : Type u} (R : RawGroupStructure G) (S : RawGroupStructure H) where
  toEquiv : G ≃ H
  map_zero : toEquiv R.zero = S.zero
  map_neg : ∀ x, toEquiv (R.neg x) = S.neg (toEquiv x)
  map_add : ∀ x y, toEquiv (R.add x y) = S.add (toEquiv x) (toEquiv y)

def RawScottSentence {G : Type u} (R : RawGroupStructure G) (φ : Formula 0) : Prop :=
  φ.RawRealize R Fin.elim0 ∧ ∀ (H : Type u) [Countable H] (S : RawGroupStructure H),
    φ.RawRealize S Fin.elim0 → Nonempty (RawIsomorphism R S)

def RawDifferenceScottSentence {G : Type u} (R : RawGroupStructure G) (d : DifferenceFormula 0) : Prop :=
  d.RawRealize R Fin.elim0 ∧ ∀ (H : Type u) [Countable H] (S : RawGroupStructure H),
    d.RawRealize S Fin.elim0 → Nonempty (RawIsomorphism R S)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
