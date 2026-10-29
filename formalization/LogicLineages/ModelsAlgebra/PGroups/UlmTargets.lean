module

public import LogicLineages.ModelsAlgebra.PGroups.UlmMapDefinitions

@[expose] public section

/-!
Fixed nontrivial local isomorphism obligation for the second half of
paper 01's `lem:quotient-filtration`. The map is the already constructed
actual map induced by f on actual p-socle quotients. Kernel containment
in the second successor subgroup is the genuine local form of the
source's deep-kernel hypothesis. Its derivation at every beta below
omega*gamma and the final rank identity remain separate obligations.
-/

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

universe u v

def localUlmMapBijective : Prop :=
  ∀ (G : Type u) (H : Type v) [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) (S : AddSubgroup G) (f : G →+ H),
    f.ker ≤ pStep p (pStep p S) → Function.Bijective (ulmMap p S f)

end LogicLineages.ModelsAlgebra.PGroups.Targets
