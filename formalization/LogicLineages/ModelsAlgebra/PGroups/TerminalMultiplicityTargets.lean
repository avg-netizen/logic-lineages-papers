module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalMultiplicityDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def terminalMultiplicityData : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G] (n:ℕ),
    0<n → (∀x:G,p^n • x=0) → (∃x:G,p^(n-1) • x≠0) →
    ∃ I:Fin n→Type, Nonempty (G≃+CyclicRootSum p n I) ∧
      (∀j:Fin n, Cardinal.mk (I j)=Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val:AddSubgroup G))) ∧
      (∀j:Fin n, Cardinal.mk (I j)≤Cardinal.aleph0) ∧
      (∀j:Fin n, j.val=n-1 → Cardinal.mk (I j)≠0)
end LogicLineages.ModelsAlgebra.PGroups.Targets
