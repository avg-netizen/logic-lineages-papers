module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleWindowDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Each actual bounded p-torsion layer is finite when the actual socle is finite. -/
def finiteSoclePowerTorsion : Prop :=
  ∀ (G:Type) [AddCommGroup G] (p:ℕ)
    [Finite (pSocle p (⊤:AddSubgroup G))] (n:ℕ), Finite (powerTorsion G p n)
/-- Finite socle gives an actual finite stable filtration stage, including a
possibly nonzero finite-rank divisible part. -/
def finiteSocleFiniteStable : Prop :=
  ∀ (G:Type) [AddCommGroup G] [Countable G] (p:ℕ) [Fact p.Prime]
    [Finite (pSocle p (⊤:AddSubgroup G))],
    (∀x:G,∃k:ℕ,p^k • x=0) → ∃n:ℕ, StableAt p G (n:Ordinal.{0})
/-- Every finite tuple is contained in an actual finite subgroup whose
EVERY injective hom into the original group extends on that tuple to an
actual whole-group automorphism. No embedding/orbit supplier is input. -/
def finiteSocleEmbeddingWindow : Prop :=
  ∀ (G:Type) [AddCommGroup G] [Countable G] (p:ℕ) [Fact p.Prime]
    [Finite (pSocle p (⊤:AddSubgroup G))],
    (∀x:G,∃k:ℕ,p^k • x=0) →
    ∀ (A:AddSubgroup G) [Finite A],
      ∃ (B:AddSubgroup G), Finite B ∧ ∃hAB:A≤B,
        ∀ (f:B→+G), Function.Injective f →
          ∃u:G≃+G, ∀x:A, u x=f ⟨(x:G),hAB x.property⟩
end LogicLineages.ModelsAlgebra.PGroups.Targets
