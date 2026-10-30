module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenamingDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
universe u v

def groupTermRenamingEvaluation : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n n' : ℕ) (ρ : Fin n → Fin n')
    (t : GroupTerm n) (a : Fin n' → G),
      (renameTerm ρ t).eval a = t.eval (fun i => a (ρ i))

def groupQFRenamingRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n n' : ℕ) (ρ : Fin n → Fin n')
    (q : QF n) (a : Fin n' → G),
      (renameQF ρ q).Realize a ↔ q.Realize (fun i => a (ρ i))

def groupLiftRenamingAssignment : Prop :=
  ∀ (G : Type u) (n n' m : ℕ) (ρ : Fin n → Fin n') (a : Fin n' → G) (d : Fin m → G),
    (fun i => append a d (liftRenaming ρ m i)) = append (fun i => a (ρ i)) d

def groupInfinitaryRenamingRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n n' : ℕ) (ρ : Fin n → Fin n')
    (φ : Formula n) (a : Fin n' → G),
      (renameFormula ρ φ).Realize a ↔ φ.Realize (fun i => a (ρ i))

def groupInfinitaryRenamingComplexity : Prop :=
  ∀ (side : Polarity) (α : Ordinal.{v}) (n n' : ℕ) (ρ : Fin n → Fin n') (φ : Formula n),
    Complexity side α φ → Complexity side α (renameFormula ρ φ)

end LogicLineages.ModelsAlgebra.PGroups.Targets
