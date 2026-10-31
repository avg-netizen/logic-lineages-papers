module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalPointedAbsorptionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
def terminalPointedAbsorption : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime]
    (S K T : AddSubgroup G) (N b : ℕ), S=K⊔T → Disjoint K T →
    (∀ x : S, p^N • x=0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b : AddSubgroup K)) = Cardinal.aleph0 →
    (∀ x : T, p^(b+1) • x=0) →
    ∀ (n : ℕ) (a : Fin n → S) (c : Fin n → K), (∀ i, (a i:G)=(c i:G)) →
      BackAndForth (2:Ordinal.{0}) a c
end LogicLineages.ModelsAlgebra.PGroups.Targets
