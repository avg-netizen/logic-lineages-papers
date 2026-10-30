module

public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimitDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupLimitAnnihilation : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G) (c : ℕ),
    (∀ x : G, c • x = 0) → ∀ z : EndomorphismLimit f, c • z = 0

/-- Source root calculation at the next actual stage. The explicit
endomorphism hypothesis still has to be proved for the source example. -/
def groupLimitSocleRoots : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G), Function.Injective f →
    ∀ (p c : ℕ), (∀ x : G, p • x = 0 → ∃ y : G, c • y = f x) →
      ∀ z : EndomorphismLimit f, p • z = 0 → ∃ y : EndomorphismLimit f, c • y = z

end LogicLineages.ModelsAlgebra.PGroups.Targets
