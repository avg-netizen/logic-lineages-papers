module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteDivisibleImageDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- An actual finite-socle divisible image, preserving every element of a given finite subgroup. -/
def finiteDivisibleImage : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Type) [AddCommGroup D],
    (∀ x : D, ∃ k : ℕ, p^k • x = 0) → GroupDivisible D →
    ∀ (S : AddSubgroup D) [Finite S],
      ∃ n : ℕ, ∃ f : D →+ (Fin n → PrueferModel p),
        Function.Injective (f.comp S.subtype) ∧ GroupDivisible f.range ∧
        Finite (pSocle p (⊤ : AddSubgroup f.range)) ∧
        Nonempty ((D ⧸ f.ker) ≃+ f.range)
end LogicLineages.ModelsAlgebra.PGroups.Targets
