module

public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteDefinitions
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

/-!
Independent fixed statements for the actual ordinal-recursive filtration
in paper 01, conventions and Lemma `lem:quotient-filtration`. The
image theorem is generalized to arbitrary surjections and arbitrary
ordinal cuts. Antitonicity is a conclusion, not an extra supplier.
The Ulm-quotient assertion and full Scott classification remain separate.
-/

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

universe u v w

def transfiniteFiltrationAntitone : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ),
    Antitone (fun α : Ordinal.{w} => (transfiniteFiltration p α : AddSubgroup G))

def transfiniteFiltrationImageBelowCut : Prop :=
  ∀ (G : Type u) (H : Type v) [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) (f : G →+ H), Function.Surjective f →
    ∀ δ : Ordinal.{w}, f.ker ≤ transfiniteFiltration p δ →
    ∀ α ≤ δ, (transfiniteFiltration p α : AddSubgroup G).map f =
      (transfiniteFiltration p α : AddSubgroup H)

end LogicLineages.ModelsAlgebra.PGroups.Targets
