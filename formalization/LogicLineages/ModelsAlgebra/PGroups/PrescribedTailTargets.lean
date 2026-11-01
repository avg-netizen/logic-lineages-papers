module
public import LogicLineages.ModelsAlgebra.PGroups.PrescribedTailDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- The actual initial Ulm factor at every earlier omega-block is primary,
reduced, countable, and unbounded; its finite Ulm ranks agree exactly with
the shifted ranks of the original group. -/
def initialUlmFactorAdmissibility : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}),
    (∀x:G,∃k:ℕ,p^k • x=0) → IsReducedAddGroup G →
    StagesNonzeroBelow p G (Ordinal.omega0*γ) →
    ∀ξ:Ordinal.{0},ξ<γ →
      Countable (UlmFactor p G ξ) ∧
      (∀x:UlmFactor p G ξ,∃k:ℕ,p^k • x=0) ∧
      IsReducedAddGroup (UlmFactor p G ξ) ∧
      (∀N:ℕ,∃x:UlmFactor p G ξ,p^N • x≠0) ∧
      ∀n:ℕ,Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (n:Ordinal.{0}):AddSubgroup (UlmFactor p G ξ)))=
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*ξ+n):AddSubgroup G))
/-- ENTIRE original prescribed-tail existence target. All Ulm and tail
objects are literal actual groups; no realization/admissibility oracle is
supplied. This stays pending until a real existence construction is proved. -/
def transfinitePrescribedTailExistence : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G T:Type) [AddCommGroup G] [AddCommGroup T]
    [Countable G] [Countable T] [Nontrivial T]
    (γ:Ordinal.{0}) [Countable γ.ToType] (ellG ellT:Ordinal.{0}),
    (∀x:G,∃k:ℕ,p^k • x=0) → (∀x:T,∃k:ℕ,p^k • x=0) →
    IsReducedAddGroup G → IsReducedAddGroup T → 0<γ →
    PGroupExactLength p G ellG → Ordinal.omega0*γ≤ellG → PGroupExactLength p T ellT →
    ∃ (H:Type) (inst:AddCommGroup H), letI:=inst; Countable H ∧
      (∀x:H,∃k:ℕ,p^k • x=0) ∧ IsReducedAddGroup H ∧
      UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) ∧
      Nonempty ((transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup H)≃+T) ∧
      PGroupExactLength p H (Ordinal.omega0*γ+ellT)
end LogicLineages.ModelsAlgebra.PGroups.Targets
