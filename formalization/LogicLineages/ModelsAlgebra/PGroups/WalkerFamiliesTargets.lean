module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFamiliesDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Exact source terminal-groups display, with actual countability and zero bounds.
Valid for every countable δ, thus in particular δ=ωγ. No complexity or Ulm-table claim. -/
def walkerSourceFamilies : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ δ : Ordinal.{0}, ∀ [Countable δ.ToType], ∀ r : ℕ,
    Countable (WalkerOdd p δ r) ∧ Countable (WalkerEven p δ r) ∧
    Nonempty ((transfiniteFiltration p δ : AddSubgroup (WalkerOdd p δ r)) ≃+ (Fin r → ZMod p)) ∧
    Nonempty ((transfiniteFiltration p δ : AddSubgroup (WalkerEven p δ r)) ≃+
      ((Fin r → ZMod p) × DirectSum ℕ (fun _ => ZMod (p^2)))) ∧
    (transfiniteFiltration p (δ+1) : AddSubgroup (WalkerOdd p δ r)) = ⊥ ∧
    (transfiniteFiltration p (δ+2) : AddSubgroup (WalkerEven p δ r)) = ⊥
end LogicLineages.ModelsAlgebra.PGroups.Targets
