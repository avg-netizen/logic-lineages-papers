module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableDefinitions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
open scoped BigOperators
universe u

/-- The actual finite p-filtration equals the ordinary p^j-multiple image. -/
def groupFiniteFiltrationMultipleImage : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p j : ℕ),
    (finiteFiltration p j : AddSubgroup G) = multipleImage G (p ^ j)

/-- A finite F_p linear combination of actual quotient classes vanishes
exactly when its representative combination belongs to the next subgroup.
The representatives are in the actual p-socle, not arbitrary group elements. -/
def groupUlmFiniteCombinationKernel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] (S : AddSubgroup G)
    (m : ℕ) (x : Fin m → pSocle p S) (r : Fin m → ZMod p),
      (∑ i, r i • (QuotientAddGroup.mk' (successorSocleSubgroup p S) (x i) : UlmLayer p S)) = 0 ↔
        (∑ i, (r i).val • (x i : G)) ∈ pStep p S

/-- Source finite Ulm lower-dimension criterion. Index j is source j+1:
P_j=(p^j G)[p], with quotient by P_(j+1). Genuine quotient independence is
characterized, not replaced by a custom independence definition. -/
def groupUlmFiniteIndependence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] (j m : ℕ)
    (x : Fin m → pSocle p (finiteFiltration p j : AddSubgroup G)),
      LinearIndependent (ZMod p)
        (fun i => (QuotientAddGroup.mk'
          (successorSocleSubgroup p (finiteFiltration p j : AddSubgroup G)) (x i) :
            UlmLayer p (finiteFiltration p j : AddSubgroup G))) ↔
        ∀ r : Fin m → ZMod p, r ≠ 0 →
          (∑ i, (r i).val • (x i : G)) ∉ finiteFiltration p (j + 1)

end LogicLineages.ModelsAlgebra.PGroups.Targets
