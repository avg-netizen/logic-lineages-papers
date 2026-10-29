module

public import LogicLineages.ModelsAlgebra.PGroups.FiltrationDefinitions
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

/-!
Independent source obligations for paper 01, Lemma
`lem:quotient-filtration`. The successor and saturated-intersection
components below do not yet constitute transfinite filtration or the
Ulm quotient isomorphism. Surjectivity and kernel containment are the
actual quotient-map input conditions, not supplied target conclusions.
-/

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

universe u v w

def subgroupImageCommutesWithPStep : Prop :=
  ∀ (G : Type u) (H : Type v) [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) (f : G →+ H) (S : AddSubgroup G),
    (pStep p S).map f = pStep p (S.map f)

def finiteFiltrationImage : Prop :=
  ∀ (G : Type u) (H : Type v) [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) (f : G →+ H), Function.Surjective f →
    ∀ n, (finiteFiltration p n : AddSubgroup G).map f =
      (finiteFiltration p n : AddSubgroup H)

def saturatedIntersectionImage : Prop :=
  ∀ (G : Type u) (H : Type v) (ι : Sort w)
    [AddCommGroup G] [AddCommGroup H] (f : G →+ H),
    Function.Surjective f →
    ∀ S : ι → AddSubgroup G, (∀ i, f.ker ≤ S i) →
      (iInf S).map f = ⨅ i, (S i).map f

end LogicLineages.ModelsAlgebra.PGroups.Targets
