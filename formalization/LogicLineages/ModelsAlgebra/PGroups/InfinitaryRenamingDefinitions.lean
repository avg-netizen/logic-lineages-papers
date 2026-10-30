module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions

@[expose] public section

/-! Capture-avoiding free-variable renaming for actual normal forms.
Bound variables stay in their new appended block; the old free variables
are transported by the given finite map. No original syntax is changed. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth

def renameTerm {n n' : ℕ} (ρ : Fin n → Fin n') : GroupTerm n → GroupTerm n'
  | .var i => .var (ρ i)
  | .zero => .zero
  | .neg t => .neg (renameTerm ρ t)
  | .add s t => .add (renameTerm ρ s) (renameTerm ρ t)

def renameQF {n n' : ℕ} (ρ : Fin n → Fin n') : QF n → QF n'
  | .equal s t => .equal (renameTerm ρ s) (renameTerm ρ t)
  | .falsum => .falsum
  | .neg q => .neg (renameQF ρ q)
  | .and q r => .and (renameQF ρ q) (renameQF ρ r)

def liftRenaming {n n' : ℕ} (ρ : Fin n → Fin n') (m : ℕ) : Fin (n + m) → Fin (n' + m) :=
  Fin.addCases (fun i => Fin.castAdd m (ρ i)) (Fin.natAdd n')

def renameFormula {n n' : ℕ} (ρ : Fin n → Fin n') : Formula n → Formula n'
  | .qf q => .qf (renameQF ρ q)
  | .disjEx s m matrix => .disjEx s m (fun i => renameFormula (liftRenaming ρ (m i)) (matrix i))
  | .conjAll s m matrix => .conjAll s m (fun i => renameFormula (liftRenaming ρ (m i)) (matrix i))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
