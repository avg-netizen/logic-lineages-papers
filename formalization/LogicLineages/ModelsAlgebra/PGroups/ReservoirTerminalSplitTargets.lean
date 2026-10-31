module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirTerminalSplitDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def reservoirComplementSplit : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (i : ℕ),
    Disjoint (reservoirStage A B C i) (reservoirComplement A B C i) ∧
    reservoirStage A B C i ⊔ reservoirComplement A B C i = ⊤ ∧
    ∀ d : ℕ, (∀ x : B, d • x=0) → ∀ x : reservoirComplement A B C i, d • x=0

def reservoirAmbientSplit : Prop :=
  ∀ (G A B C : Type) [AddCommGroup G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (S : AddSubgroup G) (e : S ≃+ ReservoirGroup A B C) (i d : ℕ),
    (∀ x : B, d • x=0) → ∃ K T : AddSubgroup G,
    S=K⊔T ∧ Disjoint K T ∧ Nonempty (K ≃+ reservoirStage A B C i) ∧
    (∀ x : T, d • x=0) ∧ ∀ x : S, (x:G) ∈ K ↔ e x ∈ reservoirStage A B C i
end LogicLineages.ModelsAlgebra.PGroups.Targets
