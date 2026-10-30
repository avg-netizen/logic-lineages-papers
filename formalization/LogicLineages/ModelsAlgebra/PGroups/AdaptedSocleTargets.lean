module

public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocleDefinitions
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupAdaptedSocleIndependent : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (N : ℕ) (I : Fin N → Type)
    (b : ∀ l : Fin N, Module.Basis (I l) (ZMod p) (UlmLayer p (finiteFiltration p l.val : AddSubgroup G)))
    (x : ∀ l : Fin N, I l → pSocle p (finiteFiltration p l.val : AddSubgroup G)),
    (∀ l i, QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p l.val)) (x l i) = b l i) →
      LinearIndependent (ZMod p) (includedSocleFamily p N I x)

/-- Filtered spanning, not merely spanning the unfiltered whole socle. -/
def groupAdaptedSocleFilteredSpan : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (N : ℕ),
    (∀ g : G, p ^ N • g = 0) → ∀ (I : Fin N → Type)
    (b : ∀ l : Fin N, Module.Basis (I l) (ZMod p) (UlmLayer p (finiteFiltration p l.val : AddSubgroup G)))
    (x : ∀ l : Fin N, I l → pSocle p (finiteFiltration p l.val : AddSubgroup G)),
    (∀ l i, QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p l.val)) (x l i) = b l i) →
      ∀ j : ℕ, j ≤ N → socleLevel p G j =
        Submodule.span (ZMod p) (Set.range (fun a : {a : (Σ l : Fin N, I l) // j ≤ a.1.val} =>
          includedSocleFamily p N I x a.val))

end LogicLineages.ModelsAlgebra.PGroups.Targets
